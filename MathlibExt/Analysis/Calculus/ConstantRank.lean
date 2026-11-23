/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# The constant rank theorem

If `f : E → F` between finite-dimensional real normed spaces is `Cⁿ` (`1 ≤ n`) on an open
set `U ∋ x` and the rank of `fderiv ℝ f y` equals `r` for all `y` in a neighbourhood of `x`,
then there are centred `Cⁿ` coordinate changes `φ` near `x` (inside `U`) and `ψ` near `f x`
in which `f` reads `(u, v) ↦ (u, 0)`, with `u ∈ ℝʳ`. In these coordinates each local fibre
of `f` is an open piece of an affine slice `{u fixed}`, with free coordinate in
`ℝ^(dim E - r)`. `exists_constantRank_coordinates_euclidean` is the `ℝᵈ → ℝᵐ` form with the
literal normal form `(u₁, …, u_d) ↦ (u₁, …, u_r, 0, …, 0)`.

The rank hypothesis must hold on a neighbourhood: rank `r` only at `x` does not suffice
(e.g. `t ↦ t²` at `0`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Ch. 4
  (constant rank theorem).
* L. W. Tu, *An Introduction to Manifolds*, 2nd ed., Springer, 2011, Thm 11.1.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace MathlibExt.Analysis.Calculus.ConstantRank

/-- Given (already proved; may be used): in the normal form `(u, v) ↦ (u, 0)`, each local fibre
of `f` is mapped by `φ` onto the slice of `φ.target` with first coordinate fixed. -/
private theorem image_fiber_eq_slice {E F R K C : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace R] [TopologicalSpace K] [TopologicalSpace C] [Zero C] {f : E → F}
    (φ : OpenPartialHomeomorph E (R × K)) (ψ : OpenPartialHomeomorph F (R × C))
    (hmaps : MapsTo f φ.source ψ.source)
    (hnf : ∀ p ∈ φ.target, ψ (f (φ.symm p)) = (p.1, 0)) :
    ∀ y ∈ φ.source, φ '' (φ.source ∩ f ⁻¹' {f y}) = φ.target ∩ {p | p.1 = (φ y).1} := by
  have key : ∀ z ∈ φ.source, ψ (f z) = ((φ z).1, 0) := fun z hz => by
    simpa only [φ.left_inv hz] using hnf (φ z) (φ.map_source hz)
  intro y hy
  ext p
  constructor
  · rintro ⟨z, ⟨hz, hfz⟩, rfl⟩
    have hfz' : f z = f y := hfz
    refine ⟨φ.map_source hz, ?_⟩
    have h := (key z hz).symm.trans ((congrArg ψ hfz').trans (key y hy))
    exact (Prod.ext_iff.mp h).1
  · rintro ⟨hp, hp1⟩
    have hp1' : p.1 = (φ y).1 := hp1
    refine ⟨φ.symm p, ⟨φ.map_target hp, ?_⟩, φ.right_inv hp⟩
    show f (φ.symm p) = f y
    apply ψ.injOn (hmaps (φ.map_target hp)) (hmaps hy)
    rw [key _ (φ.map_target hp), key y hy, φ.right_inv hp, hp1']

/-- A linear surjection `L : V → ℝʳ` is the first component of a continuous linear equivalence
`V ≃ ℝʳ × ℝ^(dim V - r)`. -/
private theorem exists_equiv_fst_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {r : ℕ} (L : V →ₗ[ℝ] EuclideanSpace ℝ (Fin r))
    (hL : Function.Surjective L) :
    ∃ e : V ≃L[ℝ] EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ V - r)),
      ∀ v, (e v).1 = L v := by
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hL, finrank_top, finrank_euclideanSpace_fin] at hrn
  have hk : Module.finrank ℝ (LinearMap.ker L) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V - r))) := by
    rw [finrank_euclideanSpace_fin]; omega
  obtain ⟨M, hM⟩ := LinearMap.exists_extend (LinearEquiv.ofFinrankEq _ _ hk).toLinearMap
  have hinj : Function.Injective (L.prod M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : L v = 0 := congrArg Prod.fst hv
    have h2 : M v = 0 := congrArg Prod.snd hv
    have h3 := congrArg (fun g => g ⟨v, LinearMap.mem_ker.mpr h1⟩) hM
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, h2] at h3
    have := (LinearEquiv.ofFinrankEq _ _ hk).injective (h3.symm.trans (map_zero _).symm)
    simpa using congrArg Subtype.val this
  have hsurj : Function.Surjective (L.prod M) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
      omega)).mp hinj
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun v => rfl⟩

/-- If `L` has rank `r` and `P ∘ L` maps onto `ℝʳ`, then `P` is injective on the range of `L`. -/
private theorem apply_eq_zero_of_comp_surjective {V F : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F] {r : ℕ}
    (L : V →ₗ[ℝ] F) (P : F →ₗ[ℝ] EuclideanSpace ℝ (Fin r))
    (hL : Module.finrank ℝ (LinearMap.range L) = r) (hPL : Function.Surjective (P ∘ₗ L))
    {v : V} (hv : P (L v) = 0) : L v = 0 := by
  have hsurj : Function.Surjective (P.domRestrict (LinearMap.range L)) := by
    intro u
    obtain ⟨w, hw⟩ := hPL u
    exact ⟨⟨L w, LinearMap.mem_range_self L w⟩, hw⟩
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [hL, finrank_euclideanSpace_fin])).mpr hsurj
  have : (⟨L v, LinearMap.mem_range_self L v⟩ : LinearMap.range L) = 0 :=
    hinj (by simpa using hv)
  simpa using congrArg Subtype.val this

/-- If `γ` is a `Cⁿ` section on the open set `B`, in the sense that `(β (γ u - c)).1 = u`, then
`w ↦ ((β (w - c)).1, (β (w - γ (β (w - c)).1)).2)` is a `Cⁿ` chart sending `γ u` to `(u, 0)`. -/
private theorem exists_chart_of_section {F R C : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [NormedAddCommGroup C] [NormedSpace ℝ C]
    {n : WithTop ℕ∞} (β : F ≃L[ℝ] R × C) (c : F) {B : Set R} (hB : IsOpen B) {γ : R → F}
    (hγ : ContDiffOn ℝ n γ B) (hγβ : ∀ u ∈ B, (β (γ u - c)).1 = u) :
    ∃ ψ : OpenPartialHomeomorph F (R × C), ψ.source = {w | (β (w - c)).1 ∈ B} ∧
      (∀ u ∈ B, ψ (γ u) = (u, 0)) ∧ ContDiffOn ℝ n ψ ψ.source ∧
      ContDiffOn ℝ n ψ.symm ψ.target := by
  have hpC : ContDiff ℝ n (fun w : F => (β (w - c)).1) :=
    (ContinuousLinearMap.fst ℝ R C).contDiff.comp
      (β.contDiff.comp (contDiff_id.sub contDiff_const))
  have hto : ContDiffOn ℝ n (fun w => ((β (w - c)).1, (β (w - γ (β (w - c)).1)).2))
      {w | (β (w - c)).1 ∈ B} := by
    have h1 : ContDiffOn ℝ n (fun w => γ (β (w - c)).1) {w | (β (w - c)).1 ∈ B} :=
      hγ.comp hpC.contDiffOn (fun w hw => hw)
    refine hpC.contDiffOn.prodMk ?_
    exact (ContinuousLinearMap.snd ℝ R C).contDiff.comp_contDiffOn
      (β.contDiff.comp_contDiffOn (contDiffOn_id.sub h1))
  have hinv : ContDiffOn ℝ n (fun q : R × C => γ q.1 + β.symm (0, q.2)) (B ×ˢ univ) := by
    have h1 : ContDiffOn ℝ n (fun q : R × C => γ q.1) (B ×ˢ univ) :=
      hγ.comp contDiffOn_fst (fun q hq => hq.1)
    exact h1.add (β.symm.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn
  have key : ∀ q : R × C, q.1 ∈ B → (β (γ q.1 + β.symm (0, q.2) - c)).1 = q.1 := by
    intro q hq
    have : γ q.1 + β.symm (0, q.2) - c = (γ q.1 - c) + β.symm (0, q.2) := by abel
    rw [this, map_add, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_add, hγβ q.1 hq, add_zero]
  refine ⟨{ toFun := fun w => ((β (w - c)).1, (β (w - γ (β (w - c)).1)).2)
            invFun := fun q => γ q.1 + β.symm (0, q.2)
            source := {w | (β (w - c)).1 ∈ B}
            target := B ×ˢ univ
            map_source' := fun w hw => ⟨hw, trivial⟩
            map_target' := fun q hq => by
              show (β (γ q.1 + β.symm (0, q.2) - c)).1 ∈ B
              rw [key q hq.1]; exact hq.1
            left_inv' := ?_
            right_inv' := ?_
            open_source := hB.preimage hpC.continuous
            open_target := hB.prod isOpen_univ
            continuousOn_toFun := hto.continuousOn
            continuousOn_invFun := hinv.continuousOn }, rfl, ?_, hto, hinv⟩
  · intro w hw
    have hz : (β (w - γ (β (w - c)).1)).1 = 0 := by
      have : w - γ (β (w - c)).1 = (w - c) - (γ (β (w - c)).1 - c) := by abel
      rw [this, map_sub, Prod.fst_sub, hγβ _ hw, sub_self]
    show γ (β (w - c)).1 + β.symm (0, (β (w - γ (β (w - c)).1)).2) = w
    have : ((0 : R), (β (w - γ (β (w - c)).1)).2) = β (w - γ (β (w - c)).1) := Prod.ext hz.symm rfl
    rw [this, ContinuousLinearEquiv.symm_apply_apply]; abel
  · intro q hq
    show ((β (γ q.1 + β.symm (0, q.2) - c)).1,
      (β (γ q.1 + β.symm (0, q.2) - γ (β (γ q.1 + β.symm (0, q.2) - c)).1)).2) = q
    rw [key q hq.1, add_sub_cancel_left, ContinuousLinearEquiv.apply_symm_apply]
  · intro u hu
    show ((β (γ u - c)).1, (β (γ u - γ (β (γ u - c)).1)).2) = (u, 0)
    rw [hγβ u hu, sub_self, map_zero]; rfl

/-- Restriction of an open partial homeomorphism to an open subset of its target. -/
private theorem exists_restr_target {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Φ : OpenPartialHomeomorph X Y) {B : Set Y} (hB : IsOpen B) (hBt : B ⊆ Φ.target) :
    ∃ φ : OpenPartialHomeomorph X Y, φ.source = Φ.source ∩ Φ ⁻¹' B ∧ φ.target = B ∧
      ⇑φ = ⇑Φ ∧ ⇑φ.symm = ⇑Φ.symm :=
  ⟨Φ.trans (OpenPartialHomeomorph.ofSet B hB), by simp,
    by simp [inter_eq_left.mpr hBt], by simp, by simp⟩

/-- **Constant rank theorem.** Let `E`, `F` be finite-dimensional real normed spaces, `U ⊆ E`
open, `x ∈ U`, and `f : E → F` of class `Cⁿ` on `U` with `1 ≤ n`. If the derivative of `f` has
rank `r` at every point of a neighbourhood of `x`, there are `Cⁿ` charts `φ` (around `x`, inside
`U`) and `ψ` (around `f x`), centred at `x` and `f x`, with `f` mapping the source of `φ` into
the source of `ψ`, in which `f` reads `(u, v) ↦ (u, 0)`. Each local fibre of `f` is mapped by `φ`
onto the slice of `φ.target` where the `ℝʳ` coordinate is fixed; the free coordinate ranges over
an open subset of `ℝ^(dim E - r)`. -/
theorem exists_constantRank_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {n : WithTop ℕ∞} (hn : 1 ≤ n) {f : E → F} {U : Set E} {x : E} {r : ℕ}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ n f U)
    (hrank : ∀ᶠ y in 𝓝 x, Module.finrank ℝ (LinearMap.range (fderiv ℝ f y : E →ₗ[ℝ] F)) = r) :
    ∃ (φ : OpenPartialHomeomorph E
          (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))))
      (ψ : OpenPartialHomeomorph F
          (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ F - r)))),
      x ∈ φ.source ∧ φ.source ⊆ U ∧ φ x = 0 ∧ ψ (f x) = 0 ∧
      ContDiffOn ℝ n φ φ.source ∧ ContDiffOn ℝ n φ.symm φ.target ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      MapsTo f φ.source ψ.source ∧
      (∀ p ∈ φ.target, ψ (f (φ.symm p)) = (p.1, 0)) ∧
      ∀ y ∈ φ.source, φ '' (φ.source ∩ f ⁻¹' {f y}) = φ.target ∩ {p | p.1 = (φ y).1} := by
  have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have hUx : U ∈ 𝓝 x := hU.mem_nhds hx
  have hfd : ∀ y ∈ U, HasFDerivAt f (fderiv ℝ f y) y := fun y hy =>
    ((hf.differentiableOn hn0).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  -- linear algebra at `x`
  have hrx : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] F)) = r :=
    hrank.self_of_nhds
  obtain ⟨eR⟩ : Nonempty (LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] F) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin r)) :=
    ⟨LinearEquiv.ofFinrankEq _ _ (by rw [hrx, finrank_euclideanSpace_fin])⟩
  obtain ⟨P₀, hP₀⟩ := LinearMap.exists_extend eR.toLinearMap
  set P : F →L[ℝ] EuclideanSpace ℝ (Fin r) := LinearMap.toContinuousLinearMap P₀
  have hPA : Function.Surjective (fun v => P (fderiv ℝ f x v)) := by
    intro u
    obtain ⟨⟨w, v, rfl⟩, hw⟩ := eR.surjective u
    refine ⟨v, ?_⟩
    have := congrArg (fun g => g ⟨fderiv ℝ f x v, v, rfl⟩) hP₀
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [← hw]
    exact this
  have hPs : Function.Surjective P := fun u =>
    let ⟨v, hv⟩ := hPA u
    ⟨fderiv ℝ f x v, hv⟩
  obtain ⟨α, hα⟩ := exists_equiv_fst_eq
    ((P.comp (fderiv ℝ f x) : E →L[ℝ] EuclideanSpace ℝ (Fin r)) :
      E →ₗ[ℝ] EuclideanSpace ℝ (Fin r)) hPA
  obtain ⟨β, hβ⟩ := exists_equiv_fst_eq (P : F →ₗ[ℝ] EuclideanSpace ℝ (Fin r)) hPs
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply] at hα hβ
  set Q := (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin r))
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r)))).comp α.toContinuousLinearMap
  -- the first chart, before shrinking
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : E → EuclideanSpace ℝ (Fin r) ×
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r)),
      ∀ y, φ₀ y = (P (f y - f x), Q y - Q x) := ⟨_, fun _ => rfl⟩
  have hφ₀f : φ₀ = fun y => (P (f y - f x), Q y - Q x) := funext hφ₀
  have hφ₀C : ContDiffOn ℝ n φ₀ U := by
    rw [hφ₀f]
    exact (P.contDiff.comp_contDiffOn (hf.sub contDiffOn_const)).prodMk
      (Q.contDiff.sub contDiff_const).contDiffOn
  have hφ₀D : ∀ y ∈ U, HasFDerivAt φ₀ ((P.comp (fderiv ℝ f y)).prod Q) y := by
    intro y hy
    rw [hφ₀f]
    exact (P.hasFDerivAt.comp y ((hfd y hy).sub_const (f x))).prodMk
      (Q.hasFDerivAt.sub_const (Q x))
  have hDx : (P.comp (fderiv ℝ f x)).prod Q = α.toContinuousLinearMap := by
    refine ContinuousLinearMap.ext fun v => Prod.ext ?_ rfl
    simp [hα]
  have hφ₀x : HasFDerivAt φ₀ (α : E →L[ℝ] _) x := hDx ▸ hφ₀D x hx
  obtain ⟨Φ, hΦcoe, hxΦ⟩ : ∃ Φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin r) ×
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))), ⇑Φ = φ₀ ∧ x ∈ Φ.source :=
    ⟨_, ContDiffAt.toOpenPartialHomeomorph_coe (hφ₀C.contDiffAt hUx) hφ₀x hn0,
      ContDiffAt.mem_toOpenPartialHomeomorph_source (hφ₀C.contDiffAt hUx) hφ₀x hn0⟩
  subst hΦcoe
  have hΦx : Φ x = 0 := by rw [hφ₀]; simp
  -- a neighbourhood of `x` where the rank is `r` and `D Φ` is invertible
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f y : E →ₗ[ℝ] F)) = r ∧
      ∃ e : E ≃L[ℝ] (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))),
        HasFDerivAt Φ (e : E →L[ℝ] _) y ∧ ∀ v, (e v).1 = P (fderiv ℝ f y v) := by
    have hc : ContinuousAt (fderiv ℝ Φ) x :=
      (hφ₀C.continuousOn_fderiv_of_isOpen hU hn).continuousAt hUx
    have hmem : fderiv ℝ Φ x ∈ Set.range (ContinuousLinearEquiv.toContinuousLinearMap :
        (E ≃L[ℝ] (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r)))) →
          _) :=
      ⟨α, by rw [(hφ₀D x hx).fderiv, hDx]⟩
    have h2 := hc.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds hmem)
    filter_upwards [hUx, h2, hrank] with y hyU hy2 hyr
    obtain ⟨e, he⟩ := hy2
    rw [(hφ₀D y hyU).fderiv] at he
    refine ⟨hyU, hyr, e, ?_, fun v => ?_⟩
    · have := hφ₀D y hyU
      rwa [← he] at this
    · have := congrArg (fun L => (L v).1) he
      simpa using this
  obtain ⟨S, hSprop, hSo, hxS⟩ := eventually_nhds_iff.mp hev
  have hWo : IsOpen (Φ.target ∩ Φ.symm ⁻¹' S) := Φ.isOpen_inter_preimage_symm hSo
  have h0W : (0 : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) ∈
      Φ.target ∩ Φ.symm ⁻¹' S := by
    refine ⟨hΦx ▸ Φ.map_source hxΦ, ?_⟩
    show Φ.symm 0 ∈ S
    rw [← hΦx, Φ.left_inv hxΦ]
    exact hxS
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo 0 h0W
  set B := Metric.ball (0 : EuclideanSpace ℝ (Fin r)) ε ×ˢ
    Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) ε with hB
  have hBW : B ⊆ Φ.target ∩ Φ.symm ⁻¹' S := by
    rw [hB, ball_prod_same]
    exact hεW
  have hBo : IsOpen B := Metric.isOpen_ball.prod Metric.isOpen_ball
  have h0B : (0 : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) ∈
      B :=
    ⟨Metric.mem_ball_self hε, Metric.mem_ball_self hε⟩
  obtain ⟨φ, hφs, hφt, hφc, hφsc⟩ := exists_restr_target Φ hBo (fun p hp => (hBW hp).1)
  -- smoothness of the inverse chart on `B`
  have hΦsCA : ∀ p ∈ B, ContDiffAt ℝ n Φ.symm p := by
    intro p hp
    obtain ⟨hpT, hpS⟩ := hBW hp
    obtain ⟨hyU, -, e, he, -⟩ := hSprop _ hpS
    exact Φ.contDiffAt_symm hpT he (hφ₀C.contDiffAt (hU.mem_nhds hyU))
  -- the rank condition kills the derivative of `f ∘ Φ.symm` in the second variable
  have hderiv : ∀ p ∈ B, ∃ L : (EuclideanSpace ℝ (Fin r) ×
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) →L[ℝ] F,
      HasFDerivAt (fun q => f (Φ.symm q)) L p ∧
        L.comp (ContinuousLinearMap.inr ℝ _ _) = 0 := by
    intro p hp
    obtain ⟨hpT, hpS⟩ := hBW hp
    obtain ⟨hyU, hyr, e, he, he1⟩ := hSprop _ hpS
    refine ⟨(fderiv ℝ f (Φ.symm p)).comp e.symm.toContinuousLinearMap,
      (hfd _ hyU).comp p (Φ.hasFDerivAt_symm hpT he), ContinuousLinearMap.ext fun w => ?_⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      zero_apply]
    have hfst : ∀ q, P (fderiv ℝ f (Φ.symm p) (e.symm q)) = q.1 := fun q => by
      rw [← he1, ContinuousLinearEquiv.apply_symm_apply]
    refine apply_eq_zero_of_comp_surjective
      (((fderiv ℝ f (Φ.symm p)).comp e.symm.toContinuousLinearMap :
        (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) →L[ℝ] F) :
          (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) →ₗ[ℝ] F)
      (P : F →ₗ[ℝ] EuclideanSpace ℝ (Fin r)) ?_ ?_ ?_
    · have hsurj : LinearMap.range ((e.symm.toContinuousLinearMap :
          (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) →L[ℝ] E) :
            (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) →ₗ[ℝ] E)
              = ⊤ :=
        LinearMap.range_eq_top.mpr e.symm.surjective
      rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp_of_range_eq_top _ hsurj]
      exact hyr
    · intro u
      exact ⟨(u, 0), hfst (u, 0)⟩
    · exact hfst (0, w)
  -- hence `f ∘ Φ.symm` does not depend on the second variable on `B`
  have hindep : ∀ p ∈ B, f (Φ.symm p) = f (Φ.symm (p.1, 0)) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hmv : ∀ w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) ε,
        HasFDerivWithinAt (fun w => f (Φ.symm (u, w))) (0 : _ →L[ℝ] F)
          (Metric.ball 0 ε) w := by
      intro w hw
      obtain ⟨L, hL, hL0⟩ := hderiv (u, w) ⟨hu, hw⟩
      have := hL.comp w (hasFDerivAt_prodMk_right u w)
      rw [hL0] at this
      exact this.hasFDerivWithinAt
    have := (convex_ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) ε
      ).norm_image_sub_le_of_norm_hasFDerivWithin_le (C := 0) hmv (fun _ _ => by simp)
        (Metric.mem_ball_self hε) hv
    simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
    exact this
  -- the section `γ` and the second chart
  set γ : EuclideanSpace ℝ (Fin r) → F := fun u => f (Φ.symm (u, 0)) with hγ
  have hmemB : ∀ u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin r)) ε,
      ((u, 0) : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) ∈ B :=
    fun u hu => ⟨hu, Metric.mem_ball_self hε⟩
  have hγC : ContDiffOn ℝ n γ (Metric.ball 0 ε) := by
    have h1 : ContDiffOn ℝ n Φ.symm B := fun p hp => (hΦsCA p hp).contDiffWithinAt
    have h2 : ContDiffOn ℝ n (fun u : EuclideanSpace ℝ (Fin r) =>
        Φ.symm ((u, 0) : EuclideanSpace ℝ (Fin r) ×
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r)))) (Metric.ball 0 ε) :=
      h1.comp (contDiffOn_id.prodMk contDiffOn_const) hmemB
    exact hf.comp h2 fun u hu => (hSprop _ (hBW (hmemB u hu)).2).1
  have hγβ : ∀ u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin r)) ε, (β (γ u - f x)).1 = u := by
    intro u hu
    have := congrArg Prod.fst (Φ.right_inv (hBW (hmemB u hu)).1)
    rw [hφ₀] at this
    rw [hβ]
    exact this
  obtain ⟨ψ, hψs, hψγ, hψC, hψsC⟩ := exists_chart_of_section β (f x) Metric.isOpen_ball hγC hγβ
  have hsrcB : ∀ y ∈ φ.source, Φ y ∈ B := fun y hy => (hφs ▸ hy).2
  have hsrcS : ∀ y ∈ φ.source, y ∈ S := fun y hy => by
    have h := hφs ▸ hy
    have := (hBW h.2).2
    rwa [mem_preimage, Φ.left_inv h.1] at this
  have hmaps : MapsTo f φ.source ψ.source := by
    intro y hy
    rw [hψs]
    show (β (f y - f x)).1 ∈ Metric.ball 0 ε
    rw [hβ]
    have := (hsrcB y hy).1
    rw [hφ₀] at this
    exact this
  have hnf : ∀ p ∈ φ.target, ψ (f (φ.symm p)) = (p.1, 0) := by
    intro p hp
    rw [hφt] at hp
    rw [hφsc, hindep p hp]
    exact hψγ p.1 hp.1
  refine ⟨φ, ψ, ?_, ?_, ?_, ?_, ?_, ?_, hψC, hψsC, hmaps, hnf,
    image_fiber_eq_slice φ ψ hmaps hnf⟩
  · rw [hφs]
    exact ⟨hxΦ, by rw [mem_preimage, hΦx]; exact h0B⟩
  · intro y hy
    exact (hSprop y (hsrcS y hy)).1
  · rw [hφc]
    exact hΦx
  · have : f x = γ 0 := by
      simp only [hγ]
      rw [← Prod.zero_eq_mk, ← hΦx, Φ.left_inv hxΦ]
    rw [this, hψγ 0 (Metric.mem_ball_self hε)]
    rfl
  · rw [hφc]
    exact hφ₀C.mono fun y hy => (hSprop y (hsrcS y hy)).1
  · rw [hφsc, hφt]
    exact fun p hp => (hΦsCA p hp).contDiffWithinAt

/-- The concatenation isomorphism `ℝʳ × ℝᵏ ≃ ℝᴺ` for `r + k = N`, in coordinates. -/
private theorem exists_euclidean_equiv {N r k : ℕ} (hk : r + k = N) :
    ∃ σ : (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin k)) ≃L[ℝ] EuclideanSpace ℝ (Fin N),
      (∀ q (i : Fin N) (hi : (i : ℕ) < r), σ q i = q.1 ⟨i, hi⟩) ∧
      ∀ p (i : Fin N), ¬ (i : ℕ) < r → σ (p, 0) i = 0 := by
  subst hk
  refine ⟨EuclideanSpace.finAddEquivProd.symm, fun q i hi => ?_, fun p i hi => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j : Fin r, i = Fin.castAdd k j := ⟨⟨i, hi⟩, Fin.ext rfl⟩
    simp
  · obtain ⟨j, rfl⟩ : ∃ j : Fin k, i = Fin.natAdd r j :=
      ⟨⟨i - r, by omega⟩, Fin.ext (by simp; omega)⟩
    simp

/-- Composition of an open partial homeomorphism with a continuous linear equivalence. -/
private theorem exists_trans_equiv {X Y Z : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (φ : OpenPartialHomeomorph X Y) (σ : Y ≃L[ℝ] Z) :
    ∃ φ' : OpenPartialHomeomorph X Z, φ'.source = φ.source ∧
      φ'.target = σ.symm ⁻¹' φ.target ∧ (∀ y, φ' y = σ (φ y)) ∧
      ∀ z, φ'.symm z = φ.symm (σ.symm z) :=
  ⟨φ.trans σ.toHomeomorph.toOpenPartialHomeomorph, by simp, by simp, fun _ => rfl,
    fun _ => rfl⟩

/-- **Constant rank theorem, `ℝᵈ → ℝᵐ` form.** For `f : ℝᵈ → ℝᵐ` of class `Cⁿ` (`1 ≤ n`) on an
open `U ∋ x` whose derivative has rank `r` on a neighbourhood of `x`, there are centred `Cⁿ`
coordinate changes `φ` of `ℝᵈ` near `x` (inside `U`) and `ψ` of `ℝᵐ` near `f x` with
`ψ (f (φ⁻¹ u)) = (u₁, …, u_r, 0, …, 0)` on the target of `φ`, and `φ` maps each local fibre of
`f` onto the slice of `φ.target` where the first `r` coordinates are fixed (the other `d - r`
coordinates are free). The guard `(i : ℕ) < d` only makes the index typecheck: the rank
hypothesis forces `r ≤ d`. -/
theorem exists_constantRank_coordinates_euclidean {d m r : ℕ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ n f U)
    (hrank : ∀ᶠ y in 𝓝 x, Module.finrank ℝ (LinearMap.range
      (fderiv ℝ f y : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) = r) :
    ∃ (φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
      (ψ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))),
      x ∈ φ.source ∧ φ.source ⊆ U ∧ φ x = 0 ∧ ψ (f x) = 0 ∧
      ContDiffOn ℝ n φ φ.source ∧ ContDiffOn ℝ n φ.symm φ.target ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      MapsTo f φ.source ψ.source ∧
      (∀ u ∈ φ.target, ∀ i : Fin m,
        ψ (f (φ.symm u)) i = if h : (i : ℕ) < r ∧ (i : ℕ) < d then u ⟨i, h.2⟩ else 0) ∧
      ∀ y ∈ φ.source, φ '' (φ.source ∩ f ⁻¹' {f y}) =
        φ.target ∩ {u | ∀ i : Fin d, (i : ℕ) < r → u i = φ y i} := by
  have hrx := hrank.self_of_nhds
  have hrd : r ≤ d := by
    have := LinearMap.finrank_range_le
      (fderiv ℝ f x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    rwa [hrx, finrank_euclideanSpace_fin] at this
  have hrm : r ≤ m := by
    have := Submodule.finrank_le (LinearMap.range
      (fderiv ℝ f x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)))
    rwa [hrx, finrank_euclideanSpace_fin] at this
  obtain ⟨φ', ψ', hx', hsU', hφx', hψx', hφC', hφsC', hψC', hψsC', hmaps', hnf', -⟩ :=
    exists_constantRank_coordinates hn hU hx hf hrank
  obtain ⟨σd, hσd, -⟩ := exists_euclidean_equiv (N := d) (r := r)
    (k := Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - r)
    (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨σm, hσm1, hσm2⟩ := exists_euclidean_equiv (N := m) (r := r)
    (k := Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) - r)
    (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨φ, hφs, hφt, hφc, hφsc⟩ := exists_trans_equiv φ' σd
  obtain ⟨ψ, hψs, hψt, hψc, hψsc⟩ := exists_trans_equiv ψ' σm
  have hnf : ∀ u ∈ φ.target, ∀ i : Fin m,
      ψ (f (φ.symm u)) i = if h : (i : ℕ) < r ∧ (i : ℕ) < d then u ⟨i, h.2⟩ else 0 := by
    intro u hu i
    rw [hφt] at hu
    rw [hφsc, hψc, hnf' _ hu]
    by_cases hi : (i : ℕ) < r
    · rw [dite_eq_left ⟨hi, by omega⟩, hσm1 _ i hi]
      have := hσd (σd.symm u) ⟨i, by omega⟩ hi
      rw [ContinuousLinearEquiv.apply_symm_apply] at this
      exact this.symm
    · rw [dite_eq_right fun h => hi h.1]
      exact hσm2 _ i hi
  have hmaps : MapsTo f φ.source ψ.source := by
    rw [hφs, hψs]
    exact hmaps'
  refine ⟨φ, ψ, hφs ▸ hx', hφs ▸ hsU', ?_, ?_, ?_, ?_, ?_, ?_, hmaps, hnf, ?_⟩
  · rw [hφc, hφx', map_zero]
  · rw [hψc, hψx', map_zero]
  · rw [hφs]
    exact (σd.contDiff.comp_contDiffOn hφC').congr fun y _ => hφc y
  · rw [hφt]
    exact (hφsC'.comp σd.symm.contDiff.contDiffOn fun u hu => hu).congr fun u _ => hφsc u
  · rw [hψs]
    exact (σm.contDiff.comp_contDiffOn hψC').congr fun y _ => hψc y
  · rw [hψt]
    exact (hψsC'.comp σm.symm.contDiff.contDiffOn fun u hu => hu).congr fun u _ => hψsc u
  · intro y hy
    have key : ∀ z ∈ φ.source, ∀ i : Fin m,
        ψ (f z) i = if h : (i : ℕ) < r ∧ (i : ℕ) < d then φ z ⟨i, h.2⟩ else 0 := by
      intro z hz i
      have := hnf (φ z) (φ.map_source hz) i
      rwa [φ.left_inv hz] at this
    ext u
    constructor
    · rintro ⟨z, ⟨hz, hfz⟩, rfl⟩
      refine ⟨φ.map_source hz, fun i hi => ?_⟩
      have h1 := key z hz ⟨i, by omega⟩
      have h2 := key y hy ⟨i, by omega⟩
      rw [show f z = f y from hfz, h2] at h1
      simpa [hi] using h1.symm
    · rintro ⟨hu, hu1⟩
      refine ⟨φ.symm u, ⟨φ.map_target hu, ?_⟩, φ.right_inv hu⟩
      show f (φ.symm u) = f y
      apply ψ.injOn (hmaps (φ.map_target hu)) (hmaps hy)
      ext i
      rw [hnf u hu i, key y hy i]
      split_ifs with h
      · exact hu1 ⟨i, h.2⟩ h.1
      · rfl

end MathlibExt.Analysis.Calculus.ConstantRank
