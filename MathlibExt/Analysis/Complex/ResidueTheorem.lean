/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.CauchyHomology
public import MathlibExt.Analysis.Complex.Residue
public import MathlibExt.Topology.Inside

/-!
# The residue theorem for a simple closed curve

Let `f` be holomorphic on an open set `Ω` except for isolated singularities, the points of a set
`S` with no accumulation point in `Ω`. Let `γ` be a positively oriented closed piecewise `C¹`
curve such that `γ` and its inside lie in `Ω` and no singularity lies on `γ`. Then only finitely
many singularities lie inside `γ`, and `(2πi)⁻¹ ∫_γ f(z) dz = ∑ Res_{z = a} f(z)`, the sum over
the singularities `a` inside `γ`.

* `Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue` is the source's statement, for a
  simple closed curve in a region.
* `Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue_of_windingNumber_eq_one` drops the
  hypotheses that the proof does not use: it holds for any open `Ω` and any closed piecewise `C¹`
  path that winds once around each point of its inside.
* `Complex.curveIntegral_eq_sum_circleIntegral`: Cauchy's theorem for a cycle
  `γ - ∑_{a ∈ F} C(a, r a)` homologous to zero, `∫_γ f(z) dz = ∑_{a ∈ F} ∮_{C(a, r a)} f(z) dz`.

The curve integral `∫_γ φ(z) dz` is Mathlib's `∫ᶜ z in γ, φ z • ContinuousLinearMap.id ℂ ℂ`, the
residue is `Complex.residue`, and the inside of `γ` is `Set.inside (range γ)`, the union of the
bounded components of `ℂ \ γ`; for a simple closed curve the Jordan curve theorem identifies it
with the interior of `γ`. Positive orientation is the hypothesis that the winding number
`Complex.windingNumber γ z` is `1` for `z` inside `γ`. For a simple closed curve the Jordan curve
theorem gives `n(γ, z) = ±1` inside, and the orientation fixes the sign. Mathlib has no Jordan
curve theorem, so the orientation hypothesis cannot be derived from simplicity here.

The proof follows the source. The singularities inside `γ` form a closed discrete subset of the
compact set `γ ∪ inside γ ⊆ Ω`, hence a finite set `F`. Small circles `C(a, r_a)`, `a ∈ F`, isolate
them, and the cycle `γ - ∑_a C(a, r_a)` is homologous to zero in `Ω \ S`: at a singularity inside
`γ` both `γ` and its circle wind once, and elsewhere off `Ω \ S` neither winds. Cauchy's theorem
for cycles (`Complex.sum_curveIntegral_eq_zero`) turns `∫_γ f` into the sum of the circle integrals,
each of which is `2πi` times a residue (`Complex.residue_eq_circleIntegral`).

Rubric-guided revision of v1 ComplexVariables target 19 (`residue_theorem` in
`v1/Atlas/ComplexVariables/code/Lecture14.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`). Archived defects fixed:
* the curve was a circle `C(c, R)`; it is now any closed piecewise `C¹` path with its inside;
* the singularities were a finite injective family in the disc, with the redundant hypotheses
  `ha` and `hinj`; they are now any set without accumulation points in `Ω`, and the finiteness of
  the singularities inside the curve is proved and stated;
* the residue `residue f a R` depended on a user-chosen radius; it is now the radius-free
  `Complex.residue`;
* `residue_theorem` was an alias of `residue_theorem_aux`, the file declared
  `circleIntegral.integral_neg` in Mathlib's namespace and needed `maxHeartbeats 3200000`;
* the proof depended on the false `sorry`ed lemma `diffContOnCl_piecewise_cauchy_extension`; the
  deformation to small circles is now Cauchy's theorem for cycles homologous to zero.

The archived formalization and its original license/provenance remain in `v1/` (the original
license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Filter Metric Set Topology
open scoped Real

namespace Complex

/-- **Cauchy's theorem for `γ - ∑ C(a, r a)`.** Let `f` be holomorphic on an open set `Ω`, let `γ`
be a closed piecewise `C¹` path in `Ω`, and let `C(a, r a)`, `a ∈ F`, be finitely many circles in
`Ω`. If the cycle `γ - ∑_{a ∈ F} C(a, r a)` is homologous to zero in `Ω`, that is
`n(γ, z) = ∑_{a ∈ F} n(C(a, r a), z)` for every `z ∉ Ω`, then
`∫_γ f(z) dz = ∑_{a ∈ F} ∮_{C(a, r a)} f(z) dz`. -/
public theorem curveIntegral_eq_sum_circleIntegral {Ω : Set ℂ} (hΩ : IsOpen Ω) {x : ℂ}
    {γ : Path x x} (hγ : γ.IsPiecewiseC1) (hγΩ : range γ ⊆ Ω) {F : Finset ℂ} {r : ℂ → ℝ}
    (hF : ∀ a ∈ F, sphere a |r a| ⊆ Ω)
    (hhom : ∀ z ∉ Ω, windingNumber γ z = ∑ a ∈ F, windingNumber (circlePath a (r a)) z)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) :
    ∫ᶜ z in γ, f z • ContinuousLinearMap.id ℂ ℂ = ∑ a ∈ F, ∮ z in C(a, r a), f z := by
  -- The cycle, indexed by `Option F`: `none` is `γ` and `some a` is `C(a, r a)`.
  let x' : Option F → ℂ := fun i => i.elim x fun a => (a : ℂ) + r a
  let γ' : ∀ i, Path (x' i) (x' i) := fun i =>
    Option.rec (motive := fun i => Path (x' i) (x' i)) γ (fun a => circlePath a (r a)) i
  let m : Option F → ℤ := fun i => i.elim 1 fun _ => -1
  have hγ' : ∀ i, (γ' i).IsPiecewiseC1 := by
    rintro (_ | a)
    · exact hγ
    · exact isPiecewiseC1_circlePath _ _
  have hγ'Ω : ∀ i, range (γ' i) ⊆ Ω := by
    rintro (_ | ⟨a, ha⟩)
    · exact hγΩ
    · exact (range_circlePath_subset _ _).trans (hF a ha)
  have hhom' : ∀ z ∉ Ω, ∑ i, (m i : ℂ) * windingNumber (γ' i) z = 0 := by
    intro z hz
    rw [Fintype.sum_option]
    change ((1 : ℤ) : ℂ) * windingNumber γ z +
      ∑ a : F, ((-1 : ℤ) : ℂ) * windingNumber (circlePath a (r a)) z = 0
    rw [hhom z hz, Finset.sum_coe_sort F (fun a => ((-1 : ℤ) : ℂ) *
      windingNumber (circlePath a (r a)) z), ← Finset.mul_sum]
    push_cast
    ring
  have key := sum_curveIntegral_eq_zero hγ' m hΩ hγ'Ω hhom' hf
  rw [Fintype.sum_option] at key
  change ((1 : ℤ) : ℂ) * (∫ᶜ z in γ, f z • ContinuousLinearMap.id ℂ ℂ) +
    ∑ a : F, ((-1 : ℤ) : ℂ) * ∫ᶜ z in circlePath a (r a), f z • ContinuousLinearMap.id ℂ ℂ =
      0 at key
  rw [Finset.sum_coe_sort F (fun a => ((-1 : ℤ) : ℂ) *
    ∫ᶜ z in circlePath a (r a), f z • ContinuousLinearMap.id ℂ ℂ), ← Finset.mul_sum] at key
  simp only [curveIntegral_circlePath] at key
  push_cast at key
  linear_combination key

/-- **Residue theorem** for a closed curve that winds once around its inside. Let `f` be
holomorphic on an open set `Ω` except at the points of a set `S` with no accumulation point in
`Ω`. Let `γ` be a closed piecewise `C¹` path such that `γ` and its inside lie in `Ω`, no point of
`S` lies on `γ`, and `n(γ, z) = 1` for `z` inside `γ`. Then `S` has finitely many points inside
`γ` and `(2πi)⁻¹ ∫_γ f(z) dz = ∑_{a ∈ S inside γ} Res_{z = a} f(z)`.

This is `Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue` without the source hypotheses
that the proof does not use. -/
public theorem two_pi_I_inv_mul_curveIntegral_eq_finsum_residue_of_windingNumber_eq_one
    {Ω S : Set ℂ} {f : ℂ → ℂ} {x : ℂ} (hΩ : IsOpen Ω) (hS : ∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ S)
    (hf : DifferentiableOn ℂ f (Ω \ S)) {γ : Path x x} (hγ : γ.IsPiecewiseC1)
    (hγ_pos : ∀ z ∈ (range γ).inside, windingNumber γ z = 1) (hγΩ : range γ ⊆ Ω)
    (hinsΩ : (range γ).inside ⊆ Ω) (hSγ : ∀ a ∈ S, a ∉ range γ) :
    (S ∩ (range γ).inside).Finite ∧
      (2 * π * I)⁻¹ * ∫ᶜ z in γ, f z • ContinuousLinearMap.id ℂ ℂ =
        ∑ᶠ a ∈ S ∩ (range γ).inside, residue f a := by
  set T := (range γ).inside
  have hKΩ : range γ ∪ T ⊆ Ω := union_subset hγΩ hinsΩ
  -- The singularities do not accumulate in `Ω`, so `Ω \ S` is open ...
  have hΩS : IsOpen (Ω \ S) := by
    refine isOpen_iff_mem_nhds.2 fun z hz => ?_
    have h1 := hS z hz.1
    rw [eventually_nhdsWithin_iff] at h1
    filter_upwards [h1, hΩ.mem_nhds hz.1] with w hw hwΩ
    exact ⟨hwΩ, fun hwS => (eq_or_ne w z).elim (fun h => hz.2 (h ▸ hwS)) fun h => hw h hwS⟩
  -- ... and only finitely many of them lie in the compact set `γ ∪ T ⊆ Ω`.
  have hfin : (S ∩ T).Finite := by
    have hSc : Sᶜ ∈ codiscreteWithin (range γ ∪ T) :=
      codiscreteWithin_mono hKΩ (mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun z hz =>
        mem_of_superset (hS z hz) subset_union_left)
    have hK : IsCompact (range γ ∪ T) := isCompact_union_inside (isCompact_range γ.continuous)
    exact (hK.finite_sdiff_of_mem_codiscreteWithin hSc).subset fun a ha =>
      ⟨Or.inr ha.2, fun h => h ha.1⟩
  -- A small closed disc around each singularity inside `γ` isolates it and misses `γ`.
  have hrad : ∀ a ∈ S ∩ T, ∃ r > 0, closedBall a r ⊆ Ω ∧
      (∀ b ∈ S, b ∈ closedBall a r → b = a) ∧ ∀ w ∈ closedBall a r, w ∉ range γ := by
    rintro a ⟨-, haT⟩
    have haΩ : a ∈ Ω := hinsΩ haT
    have h1 := hS a haΩ
    rw [eventually_nhdsWithin_iff] at h1
    have hU : {w | w ∈ Ω ∧ (w ∈ S → w = a) ∧ w ∉ range γ} ∈ 𝓝 a := by
      filter_upwards [hΩ.mem_nhds haΩ, h1,
        (isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds haT.1] with w hw1 hw2 hw3
      exact ⟨hw1, fun hwS => by_contra fun h => hw2 h hwS, hw3⟩
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 hU
    exact ⟨r, hr, fun w hw => (hrU hw).1, fun b hb hbr => (hrU hbr).2.1 hb,
      fun w hw => (hrU hw).2.2⟩
  choose! r hr0 hrΩ hrS hrγ using hrad
  set F := hfin.toFinset
  have hF : ∀ a ∈ F, sphere a |r a| ⊆ Ω \ S := by
    intro a ha w hw
    have ha' := hfin.mem_toFinset.1 ha
    rw [abs_of_pos (hr0 a ha')] at hw
    refine ⟨hrΩ a ha' (sphere_subset_closedBall hw), fun hwS => ?_⟩
    have := hrS a ha' w hwS (sphere_subset_closedBall hw)
    rw [this, mem_sphere, dist_self] at hw
    exact (hr0 a ha').ne hw
  -- The cycle `γ - ∑_{a ∈ F} C(a, r a)` is homologous to zero in `Ω \ S`.
  have hhom : ∀ z ∉ Ω \ S,
      windingNumber γ z = ∑ a ∈ F, windingNumber (circlePath a (r a)) z := by
    intro z hz
    have hzγ : z ∉ range γ := fun h => hz ⟨hγΩ h, fun hzS => hSγ z hzS h⟩
    have hcirc : ∀ a ∈ F, windingNumber (circlePath a (r a)) z = if z = a then 1 else 0 := by
      intro a ha
      have ha' := hfin.mem_toFinset.1 ha
      split_ifs with hza
      · exact windingNumber_circlePath_of_mem_ball (by rw [hza]; exact mem_ball_self (hr0 a ha'))
      · refine windingNumber_circlePath_of_notMem_closedBall (hr0 a ha').le fun hzb => hza ?_
        exact hrS a ha' z (by_contra fun hzS => hz ⟨hrΩ a ha' hzb, hzS⟩) hzb
    rw [Finset.sum_congr rfl hcirc, Finset.sum_ite_eq]
    by_cases hzT : z ∈ T
    · have hzS : z ∈ S := by_contra fun h => hz ⟨hinsΩ hzT, h⟩
      rw [ite_eq_left (hfin.mem_toFinset.2 ⟨hzS, hzT⟩), hγ_pos z hzT]
    · rw [ite_eq_right fun h => hzT (hfin.mem_toFinset.1 h).2]
      exact windingNumber_eq_zero_of_not_isBounded hγ fun hb => hzT (mem_inside.2 ⟨hzγ, hb⟩)
  have key := curveIntegral_eq_sum_circleIntegral hΩS hγ
    (fun z hz => ⟨hγΩ hz, fun hzS => hSγ z hzS hz⟩) hF hhom hf
  refine ⟨hfin, ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := hfin.mem_toFinset.1 ha
  rw [residue_eq_circleIntegral (Ω := closedBall a (r a)) (hf.mono fun w hw =>
    ⟨hrΩ a ha' hw.1, fun hwS => hw.2 (hrS a ha' w hwS hw.1)⟩) (hr0 a ha') subset_rfl, smul_eq_mul]

/-- **Residue theorem** for a simple closed curve. Let `f` be holomorphic in a region `Ω` except
for isolated singularities, the points of a set `S ⊆ Ω` with no accumulation point in `Ω`. Let
`γ` be a positively oriented simple closed piecewise `C¹` curve that, together with its inside,
lies in `Ω`, with no singularity on `γ`. Then only finitely many singularities lie inside `γ`, and
`(2πi)⁻¹ ∫_γ f(z) dz = ∑_{a ∈ S inside γ} Res_{z = a} f(z)`.

Positive orientation is the hypothesis `n(γ, z) = 1` for `z` inside `γ`. For a simple closed
curve the Jordan curve theorem gives `n(γ, z) = ±1` inside, and the orientation fixes the sign;
with orientation stated this way the proof does not use simplicity. Connectedness of `Ω`,
`S ⊆ Ω` and simplicity of `γ` are kept because the source states them; the proof does not use
them (see `Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue_of_windingNumber_eq_one`). -/
public theorem two_pi_I_inv_mul_curveIntegral_eq_finsum_residue {Ω S : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (hΩ : IsOpen Ω) (_hΩconn : IsConnected Ω) (_hSΩ : S ⊆ Ω)
    (hS : ∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ S) (hf : DifferentiableOn ℂ f (Ω \ S)) {γ : Path x x}
    (hγ : γ.IsPiecewiseC1) (_hγ_simple : InjOn γ (Iio 1))
    (hγ_pos : ∀ z ∈ (range γ).inside, windingNumber γ z = 1) (hγΩ : range γ ⊆ Ω)
    (hinsΩ : (range γ).inside ⊆ Ω) (hSγ : ∀ a ∈ S, a ∉ range γ) :
    (S ∩ (range γ).inside).Finite ∧
      (2 * π * I)⁻¹ * ∫ᶜ z in γ, f z • ContinuousLinearMap.id ℂ ℂ =
        ∑ᶠ a ∈ S ∩ (range γ).inside, residue f a :=
  two_pi_I_inv_mul_curveIntegral_eq_finsum_residue_of_windingNumber_eq_one hΩ hS hf hγ hγ_pos
    hγΩ hinsΩ hSγ

end Complex
