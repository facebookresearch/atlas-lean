/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.SystemsBiology
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The flux balance value function: piecewise linearity and shadow prices

Flux balance analysis (FBA) is the linear program `max cᵀv` subject to `S v = b`, `l ≤ v ≤ u`
(`fbaValue S l u c b`, from `MathlibExt.Biology.Dynamics.SystemsBiology`). Its dual minimizes
`b ⬝ᵥ y + u ⬝ᵥ α - l ⬝ᵥ β` over `α, β ≥ 0` with `Sᵀ y + α - β = c` (`fbaDualFeasible`).

The dual feasible set does not depend on `b`. Writing `y = y⁺ - y⁻`, it is a polyhedron in
standard form `{z ≥ 0 | L z = c}`, and a linear objective that attains its minimum on such a
polyhedron attains it at a basic point: one where no nonzero direction in the kernel of `L`
vanishes off the support of `z`. A basic point is determined by its support, so there are
finitely many. Hence the optimal value is, at every feasible `b`, the minimum of finitely
many affine functions `b ↦ y ⬝ᵥ b + κ`, one for each basic dual point.

Near an interior feasible `b` only the pieces active at `b` matter; if the optimal dual price
`y` is unique, all active pieces have slope `y`, so the value function is affine near `b` and
its derivative there is `b' ↦ y ⬝ᵥ b'` (the shadow prices of Orth, Thiele & Palsson).

## Main results

* `exists_finset_optimal_fbaDual`: a finite set of dual feasible pairs `(y, u ⬝ᵥ α - l ⬝ᵥ β)`
  containing an optimal dual solution for every feasible right-hand side.
* `exists_finset_isLeast_fbaValue`: on the feasible right-hand sides the optimal value is the
  minimum of finitely many affine functions of `b`, so it is piecewise linear.
* `hasFDerivAt_fbaValue_of_unique`: at an interior feasible `b` with a unique optimal dual
  price vector `y`, the optimal value is differentiable with derivative `b' ↦ y ⬝ᵥ b'`.

Off the feasible right-hand sides `fbaValue` is the junk value `sSup ∅ = 0`; every statement
here assumes feasibility (or an interior feasible point). Concavity and the identification of
the supergradients with the optimal dual prices are `fbaValue_concave` and
`exists_optimal_dual_iff_supergradient`.

## Not covered

The converse of the derivative statement (differentiability forces a unique optimal price), the
superdifferential at a boundary point of the feasible set, and an explicit description of the
pieces (the finite family is obtained from basic dual points, not listed).

## References

* J. D. Orth, I. Thiele, B. Ø. Palsson, "What is flux balance analysis?", Nat. Biotechnol. 28
  (2010) 245–248.
* R. T. Rockafellar, *Convex Analysis*, Princeton (1970), Thm 19.3 (polyhedral convex
  functions) and Thm 25.1 (differentiability and unique subgradients).
* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley (1986), §8.5 (minimal faces
  and vertices) and §10.4 (sensitivity analysis).
-/

@[expose] public section

namespace MathlibExt.Biology.Dynamics.SystemsBiology

open Matrix

/-! ### Basic optimal points of a standard-form polyhedron -/

section Basic

variable {ι E : Type*} [Finite ι] [AddCommGroup E] [Module ℝ E]

/-- `z` is a basic point for the linear map `L`: the only kernel direction of `L` that vanishes
wherever `z` vanishes is `0`. -/
private def IsBasicPt (L : (ι → ℝ) →ₗ[ℝ] E) (z : ι → ℝ) : Prop :=
  ∀ d : ι → ℝ, L d = 0 → (∀ i, z i = 0 → d i = 0) → d = 0

/-- A kernel direction supported in the support of `z ≥ 0` keeps `z ± ε d ≥ 0` for some
`ε > 0`. -/
private theorem exists_pos_nonneg_add_sub {z d : ι → ℝ} (hz : 0 ≤ z)
    (hd : ∀ i, z i = 0 → d i = 0) (hd0 : d ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ 0 ≤ z + ε • d ∧ 0 ≤ z - ε • d := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h
    push Not at h
    exact hd0 (funext h)
  have hS : (Finset.univ.filter fun i => d i ≠ 0).Nonempty := ⟨j, by simp [hj]⟩
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ (fun i => z i / |d i|) hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀ hmin
  have hzpos : ∀ i, d i ≠ 0 → 0 < z i := fun i hi =>
    lt_of_le_of_ne (hz i) (fun h => hi (hd i h.symm))
  refine ⟨z i₀ / |d i₀|, div_pos (hzpos i₀ hi₀) (abs_pos.2 hi₀), fun i => ?_, fun i => ?_⟩ <;>
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hi : d i = 0
    · simp only [hi, mul_zero, add_zero, sub_zero]; exact hz i
    · have h1 := hmin i hi
      have hdi := abs_pos.2 hi
      have h2 : z i₀ / |d i₀| * |d i| ≤ z i := by
        rwa [le_div_iff₀ hdi] at h1
      have h3 := neg_abs_le (d i)
      have h4 := le_abs_self (d i)
      have h5 : 0 ≤ z i₀ / |d i₀| := (div_pos (hzpos i₀ hi₀) (abs_pos.2 hi₀)).le
      nlinarith

/-- A linear objective that attains its minimum on `{z ≥ 0 | L z = c}` attains it at a basic
point. -/
private theorem exists_basic_optimal (L : (ι → ℝ) →ₗ[ℝ] E) (φ : (ι → ℝ) →ₗ[ℝ] ℝ) (c : E)
    {z : ι → ℝ} (hz : 0 ≤ z) (hLz : L z = c)
    (hopt : ∀ z' : ι → ℝ, 0 ≤ z' → L z' = c → φ z ≤ φ z') :
    ∃ z' : ι → ℝ, 0 ≤ z' ∧ L z' = c ∧ φ z' = φ z ∧ IsBasicPt L z' := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ k, ∀ z : ι → ℝ, (Finset.univ.filter fun i => z i ≠ 0).card = k → 0 ≤ z →
      L z = c → (∀ z' : ι → ℝ, 0 ≤ z' → L z' = c → φ z ≤ φ z') →
      ∃ z' : ι → ℝ, 0 ≤ z' ∧ L z' = c ∧ φ z' = φ z ∧ IsBasicPt L z' from
    H _ z rfl hz hLz hopt
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro z hk hz hLz hopt
  by_cases hbasic : IsBasicPt L z
  · exact ⟨z, hz, hLz, rfl, hbasic⟩
  simp only [IsBasicPt, not_forall] at hbasic
  obtain ⟨d, hLd, hdz, hd0⟩ := hbasic
  -- optimality forces `φ d = 0`
  obtain ⟨ε, hε, hp, hm⟩ := exists_pos_nonneg_add_sub hz hdz hd0
  have hφd : φ d = 0 := by
    have h1 := hopt _ hp (by rw [map_add, map_smul, hLd, smul_zero, add_zero, hLz])
    have h2 := hopt _ hm (by rw [map_sub, map_smul, hLd, smul_zero, sub_zero, hLz])
    rw [map_add, map_smul, smul_eq_mul] at h1
    rw [map_sub, map_smul, smul_eq_mul] at h2
    have h3 : 0 ≤ ε * φ d := by linarith
    have h4 : ε * φ d ≤ 0 := by linarith
    have := le_antisymm h4 h3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hε.ne'
    · exact h
  -- choose a sign with a negative coordinate
  obtain ⟨e, hLe, hez, hφe, hneg⟩ : ∃ e : ι → ℝ, L e = 0 ∧ (∀ i, z i = 0 → e i = 0) ∧
      φ e = 0 ∧ ∃ i, e i < 0 := by
    by_cases h : ∃ i, d i < 0
    · exact ⟨d, hLd, hdz, hφd, h⟩
    · push Not at h
      obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
        by_contra h'
        push Not at h'
        exact hd0 (funext h')
      refine ⟨-d, by rw [map_neg, hLd, neg_zero], fun i hi => by simp [hdz i hi],
        by rw [map_neg, hφd, neg_zero], j, ?_⟩
      simp only [Pi.neg_apply, neg_neg_iff_pos]
      exact lt_of_le_of_ne (h j) (Ne.symm hj)
  have hS : (Finset.univ.filter fun i => e i < 0).Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simp [hi]⟩
  obtain ⟨i₁, hi₁, hmin⟩ := Finset.exists_min_image _ (fun i => z i / -e i) hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hmin
  set t := z i₁ / -e i₁ with ht
  have ht0 : 0 ≤ t := div_nonneg (hz i₁) (by linarith)
  set z' := z + t • e with hz'
  have hz'0 : 0 ≤ z' := by
    intro i
    simp only [hz', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hi : e i < 0
    · have h1 := hmin i hi
      have h2 : t * -e i ≤ z i := by
        rwa [le_div_iff₀ (by linarith)] at h1
      linarith
    · push Not at hi
      have h1 : 0 ≤ z i := hz i
      have h2 : 0 ≤ t * e i := mul_nonneg ht0 hi
      linarith
  have hLz' : L z' = c := by rw [hz', map_add, map_smul, hLe, smul_zero, add_zero, hLz]
  have hφz' : φ z' = φ z := by rw [hz', map_add, map_smul, hφe, smul_zero, add_zero]
  have hz'i₁ : z' i₁ = 0 := by
    have hne : e i₁ ≠ 0 := hi₁.ne
    simp only [hz', ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hsub : (Finset.univ.filter fun i => z' i ≠ 0) ⊂
      (Finset.univ.filter fun i => z i ≠ 0) := by
    refine Finset.ssubset_iff_of_subset (fun i hi => ?_) |>.2 ⟨i₁, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      intro hzi
      apply hi
      simp [hz', hzi, hez i hzi]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hzi
      exact (ne_of_lt hi₁) (hez i₁ hzi)
    · simp [hz'i₁]
  obtain ⟨w, hw0, hLw, hφw, hw⟩ := ih _ (hk ▸ Finset.card_lt_card hsub) z' rfl hz'0 hLz'
    (fun z'' h0 hL => hφz' ▸ hopt z'' h0 hL)
  exact ⟨w, hw0, hLw, hφw.trans hφz', hw⟩

/-- There are finitely many basic points of `{z ≥ 0 | L z = c}`. -/
private theorem finite_basic (L : (ι → ℝ) →ₗ[ℝ] E) (c : E) :
    {z : ι → ℝ | 0 ≤ z ∧ L z = c ∧ IsBasicPt L z}.Finite := by
  classical
  have := Fintype.ofFinite ι
  refine Set.Finite.of_finite_image
    (f := fun z : ι → ℝ => Finset.univ.filter fun i => z i = 0) (Set.toFinite _) ?_
  rintro z₁ ⟨-, hL₁, hb₁⟩ z₂ ⟨-, hL₂, -⟩ heq
  have heq' : ∀ i, z₁ i = 0 ↔ z₂ i = 0 := fun i => by
    have := congrArg (fun s : Finset ι => i ∈ s) heq
    simpa using this
  have := hb₁ (z₁ - z₂) (by rw [map_sub, hL₁, hL₂, sub_self]) (fun i hi => by
    simp [hi, (heq' i).1 hi])
  exact sub_eq_zero.1 this

end Basic

/-! ### Minima of finitely many affine functions -/

section Affine

variable {m : ℕ}

/-- A function that, on a set `U`, is the minimum of finitely many affine functions
`b ↦ p.1 ⬝ᵥ b + p.2` is differentiable at an interior point `b` of `U` where every active piece
has slope `y`, with derivative `b' ↦ y ⬝ᵥ b'`. -/
private theorem hasFDerivAt_of_isLeast_affine {F : (Fin m → ℝ) → ℝ} {U : Set (Fin m → ℝ)}
    {b : Fin m → ℝ} (hb : b ∈ interior U) {T : Finset ((Fin m → ℝ) × ℝ)}
    (hT : ∀ b' ∈ U, IsLeast ((fun p : (Fin m → ℝ) × ℝ => p.1 ⬝ᵥ b' + p.2) '' (T : Set _))
      (F b'))
    {y : Fin m → ℝ} (hact : ∀ p ∈ T, p.1 ⬝ᵥ b + p.2 = F b → p.1 = y) :
    HasFDerivAt F
      (∑ i, y i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) b := by
  set Λ := ∑ i, y i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i
  have hΛ : ∀ v, Λ v = y ⬝ᵥ v := fun v => by
    simp [Λ, dotProduct]
  have hU : U ∈ nhds b := mem_interior_iff_mem_nhds.1 hb
  obtain ⟨⟨q, hqT, hq⟩, hlow⟩ := hT b (interior_subset hb)
  simp only at hq
  -- inactive pieces stay strictly above the active piece `q` near `b`
  have hev : ∀ᶠ b' in nhds b, ∀ p ∈ T, p.1 ⬝ᵥ b + p.2 ≠ F b →
      q.1 ⬝ᵥ b' + q.2 < p.1 ⬝ᵥ b' + p.2 := by
    rw [Filter.eventually_all_finset]
    intro p hpT
    by_cases hp : p.1 ⬝ᵥ b + p.2 = F b
    · exact Filter.Eventually.of_forall fun _ h => absurd hp h
    · have hgt : q.1 ⬝ᵥ b + q.2 < p.1 ⬝ᵥ b + p.2 :=
        lt_of_le_of_ne (hq ▸ hlow ⟨p, hpT, rfl⟩) (hq ▸ Ne.symm hp)
      have hc : Continuous fun b' : Fin m → ℝ => (p.1 ⬝ᵥ b' + p.2) - (q.1 ⬝ᵥ b' + q.2) := by
        fun_prop
      have := hc.continuousAt.eventually (lt_mem_nhds (a := 0) (by linarith))
      exact this.mono fun b' hb' _ => by linarith
  have heq : F =ᶠ[nhds b] fun b' => F b + Λ (b' - b) := by
    filter_upwards [hev, hU] with b' hb' hb'U
    obtain ⟨⟨p, hpT, hp⟩, hlow'⟩ := hT b' hb'U
    simp only at hp
    have hpact : p.1 ⬝ᵥ b + p.2 = F b := by
      by_contra hne
      have h1 := hb' p hpT hne
      have h2 := hlow' ⟨q, hqT, rfl⟩
      simp only at h2
      linarith
    have hy := hact p hpT hpact
    rw [hΛ, ← hp, ← hpact, hy, dotProduct_sub]
    ring
  have hd : HasFDerivAt (fun b' => F b + Λ (b' - b)) Λ b := by
    have := ((Λ.hasFDerivAt (x := b)).const_add (F b)).sub_const (Λ b)
    simpa [map_sub, add_sub_assoc] using this
  exact hd.congr_of_eventuallyEq heq

end Affine

/-! ### Flux balance analysis -/

section FluxBalance

variable {m n : ℕ}

/-- Coordinates of the standard-form dual: `y = y⁺ - y⁻`, `α`, `β`, all nonnegative. -/
private abbrev DualIdx (m n : ℕ) : Type := (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n)

/-- The price vector `y⁺ - y⁻` of a standard-form dual point. -/
private noncomputable def dualY : (DualIdx m n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun i => Sum.inl (Sum.inl i)) -
    LinearMap.funLeft ℝ ℝ (fun i => Sum.inl (Sum.inr i))

/-- The upper-bound multiplier `α` of a standard-form dual point. -/
private noncomputable def dualA : (DualIdx m n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun j => Sum.inr (Sum.inl j))

/-- The lower-bound multiplier `β` of a standard-form dual point. -/
private noncomputable def dualB : (DualIdx m n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun j => Sum.inr (Sum.inr j))

/-- The dual constraint map `z ↦ Sᵀ y + α - β`. -/
private noncomputable def dualL (S : Matrix (Fin m) (Fin n) ℝ) :
    (DualIdx m n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Sᵀ.mulVecLin ∘ₗ dualY + dualA - dualB

/-- The dual objective as a linear functional of the standard-form point. -/
private noncomputable def dualObj (l u : Fin n → ℝ) (b : Fin m → ℝ) :
    (DualIdx m n → ℝ) →ₗ[ℝ] ℝ where
  toFun z := fbaDualValue l u b (dualY z) (dualA z) (dualB z)
  map_add' z w := by
    simp only [fbaDualValue, map_add, dotProduct_add]
    ring
  map_smul' a z := by
    simp only [fbaDualValue, map_smul, dotProduct_smul, smul_eq_mul, RingHom.id_apply]
    ring

private theorem dualL_apply (S : Matrix (Fin m) (Fin n) ℝ) (z : DualIdx m n → ℝ) :
    dualL S z = Sᵀ *ᵥ dualY z + dualA z - dualB z := rfl

/-- A nonnegative standard-form point with `L z = c` is dual feasible. -/
private theorem fbaDualFeasible_of_dualL {S : Matrix (Fin m) (Fin n) ℝ} {c : Fin n → ℝ}
    {z : DualIdx m n → ℝ} (hz : 0 ≤ z) (hL : dualL S z = c) :
    fbaDualFeasible S c (dualY z) (dualA z) (dualB z) :=
  ⟨fun _ => hz _, fun _ => hz _, hL⟩

/-- **Finitely many dual solutions suffice.** There is a finite set `T` of pairs
`(y, u ⬝ᵥ α - l ⬝ᵥ β)` with `(y, α, β)` dual feasible, such that for every feasible `b` some
pair in `T` is optimal: `y ⬝ᵥ b + κ = fbaValue S l u c b`. -/
theorem exists_finset_optimal_fbaDual (S : Matrix (Fin m) (Fin n) ℝ) (l u c : Fin n → ℝ) :
    ∃ T : Finset ((Fin m → ℝ) × ℝ),
      (∀ p ∈ T, ∃ α β, fbaDualFeasible S c p.1 α β ∧ p.2 = u ⬝ᵥ α - l ⬝ᵥ β) ∧
      ∀ b : Fin m → ℝ, (fbaFeasible S l u b).Nonempty →
        ∃ p ∈ T, p.1 ⬝ᵥ b + p.2 = fbaValue S l u c b := by
  classical
  have hP := finite_basic (dualL S) c
  refine ⟨hP.toFinset.image fun z => (dualY z, u ⬝ᵥ dualA z - l ⬝ᵥ dualB z), ?_, ?_⟩
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hz0, hLz, -⟩ := hP.mem_toFinset.1 hz
    exact ⟨dualA z, dualB z, fbaDualFeasible_of_dualL hz0 hLz, rfl⟩
  · intro b hb
    obtain ⟨y₀, α₀, β₀, ⟨hα₀, hβ₀, hc₀⟩, hV₀⟩ := exists_fbaDualValue_eq (c := c) hb
    obtain ⟨v, hv, hV, -⟩ := exists_fbaValue_eq (c := c) hb
    set z₀ : DualIdx m n → ℝ := Sum.elim (Sum.elim (fun i => max (y₀ i) 0)
      (fun i => max (-y₀ i) 0)) (Sum.elim α₀ β₀) with hz₀
    have hY : dualY z₀ = y₀ := by
      funext i
      simp [dualY, hz₀]
    have hA : dualA z₀ = α₀ := by funext j; simp [dualA, hz₀, LinearMap.funLeft_apply]
    have hB : dualB z₀ = β₀ := by funext j; simp [dualB, hz₀, LinearMap.funLeft_apply]
    have hz₀0 : 0 ≤ z₀ := by
      rintro ((i | i) | (j | j)) <;>
        simp only [hz₀, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] <;>
        first | exact le_max_right _ _ | exact hα₀ j | exact hβ₀ j
    have hLz₀ : dualL S z₀ = c := by rw [dualL_apply, hY, hA, hB, hc₀]
    have hφz₀ : dualObj l u b z₀ = fbaValue S l u c b := by
      change fbaDualValue l u b (dualY z₀) (dualA z₀) (dualB z₀) = _
      rw [hY, hA, hB, hV₀]
    obtain ⟨z, hz0, hLz, hφz, hbas⟩ := exists_basic_optimal (dualL S) (dualObj l u b) c hz₀0
      hLz₀ fun z' hz' hLz' => by
        rw [hφz₀, hV]
        exact dotProduct_le_fbaDualValue hv (fbaDualFeasible_of_dualL hz' hLz')
    refine ⟨_, Finset.mem_image_of_mem _ (hP.mem_toFinset.2 ⟨hz0, hLz, hbas⟩), ?_⟩
    rw [← hφz₀, ← hφz]
    change _ = fbaDualValue l u b (dualY z) (dualA z) (dualB z)
    simp only [fbaDualValue, dotProduct_comm (dualY z) b]
    ring

/-- The finite family of `exists_finset_optimal_fbaDual` attains the minimum at every
feasible `b`. -/
private theorem isLeast_of_optimal_fbaDual {S : Matrix (Fin m) (Fin n) ℝ} {l u c : Fin n → ℝ}
    {T : Finset ((Fin m → ℝ) × ℝ)}
    (hT₁ : ∀ p ∈ T, ∃ α β, fbaDualFeasible S c p.1 α β ∧ p.2 = u ⬝ᵥ α - l ⬝ᵥ β)
    (hT₂ : ∀ b : Fin m → ℝ, (fbaFeasible S l u b).Nonempty →
      ∃ p ∈ T, p.1 ⬝ᵥ b + p.2 = fbaValue S l u c b)
    {b : Fin m → ℝ} (hb : (fbaFeasible S l u b).Nonempty) :
    IsLeast ((fun p : (Fin m → ℝ) × ℝ => p.1 ⬝ᵥ b + p.2) '' (T : Set _))
      (fbaValue S l u c b) := by
  obtain ⟨p, hpT, hp⟩ := hT₂ b hb
  refine ⟨⟨p, hpT, hp⟩, ?_⟩
  rintro _ ⟨q, hqT, rfl⟩
  obtain ⟨α, β, hd, hq⟩ := hT₁ q hqT
  obtain ⟨v, hv, hV, -⟩ := exists_fbaValue_eq (c := c) hb
  have := dotProduct_le_fbaDualValue hv hd
  simp only [fbaDualValue] at this
  change fbaValue S l u c b ≤ q.1 ⬝ᵥ b + q.2
  rw [hV, hq, dotProduct_comm q.1 b]
  linarith

/-- **The FBA value is piecewise linear.** There are finitely many affine functions
`b ↦ y ⬝ᵥ b + κ` whose minimum is the optimal value at every feasible right-hand side `b`.

Source: Rockafellar (1970), Thm 19.3; Orth, Thiele & Palsson (2010). -/
theorem exists_finset_isLeast_fbaValue (S : Matrix (Fin m) (Fin n) ℝ)
    (l u c : Fin n → ℝ) :
    ∃ T : Finset ((Fin m → ℝ) × ℝ), ∀ b : Fin m → ℝ, (fbaFeasible S l u b).Nonempty →
      IsLeast ((fun p : (Fin m → ℝ) × ℝ => p.1 ⬝ᵥ b + p.2) '' (T : Set _))
        (fbaValue S l u c b) := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_finset_optimal_fbaDual S l u c
  exact ⟨T, fun b hb => isLeast_of_optimal_fbaDual hT₁ hT₂ hb⟩

/-- **Shadow prices are derivatives when unique.** If `b` is an interior point of the set of
feasible right-hand sides and `y` is the only metabolite price vector of an optimal dual
solution, then the optimal value is differentiable at `b` with derivative `b' ↦ y ⬝ᵥ b'`.

Source: Rockafellar (1970), Thm 25.1; Orth, Thiele & Palsson (2010). -/
theorem hasFDerivAt_fbaValue_of_unique {S : Matrix (Fin m) (Fin n) ℝ}
    {l u c : Fin n → ℝ} {b : Fin m → ℝ}
    (hb : b ∈ interior {b' : Fin m → ℝ | (fbaFeasible S l u b').Nonempty}) {y : Fin m → ℝ}
    (huniq : ∀ y' : Fin m → ℝ, (∃ α β, fbaDualFeasible S c y' α β ∧
        ∀ y'' α'' β'', fbaDualFeasible S c y'' α'' β'' →
          fbaDualValue l u b y' α β ≤ fbaDualValue l u b y'' α'' β'') ↔ y' = y) :
    HasFDerivAt (fbaValue S l u c)
      (∑ i, y i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) b := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_finset_optimal_fbaDual S l u c
  have hbF : (fbaFeasible S l u b).Nonempty := (interior_subset hb :)
  refine hasFDerivAt_of_isLeast_affine hb (fun b' hb' => isLeast_of_optimal_fbaDual hT₁ hT₂ hb')
    fun p hpT hp => (huniq p.1).1 ?_
  obtain ⟨α, β, hd, hκ⟩ := hT₁ p hpT
  obtain ⟨v, hv, hV, -⟩ := exists_fbaValue_eq (c := c) hbF
  refine ⟨α, β, hd, fun y'' α'' β'' hd'' => ?_⟩
  have h1 : fbaDualValue l u b p.1 α β = fbaValue S l u c b := by
    rw [← hp, hκ, fbaDualValue, dotProduct_comm b p.1]
    ring
  rw [h1, hV]
  exact dotProduct_le_fbaDualValue hv hd''

end FluxBalance

end MathlibExt.Biology.Dynamics.SystemsBiology
