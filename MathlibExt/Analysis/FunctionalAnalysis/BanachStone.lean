/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.UrysohnsLemma

@[expose] public section

section
namespace MathlibExt.Analysis.FunctionalAnalysis.BanachStoneWanted

private lemma one_midpoint_unique
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {f g : C(X, ℝ)} (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1)
    (hfg : (2 : ℝ)⁻¹ • (f + g) = 1) : f = g := by
  ext x
  have hfx : |f x| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    exact (ContinuousMap.norm_coe_le_norm f x).trans hf
  have hgx : |g x| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    exact (ContinuousMap.norm_coe_le_norm g x).trans hg
  have hpoint := congrArg (fun k : C(X, ℝ) => k x) hfg
  change (2 : ℝ)⁻¹ * (f x + g x) = 1 at hpoint
  obtain ⟨hfl, hfu⟩ := abs_le.mp hfx
  obtain ⟨hgl, hgu⟩ := abs_le.mp hgx
  linarith

private lemma square_eq_one_of_midpoint_unique
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (u : C(X, ℝ)) (hu : ‖u‖ = 1)
    (hext : ∀ {f g : C(X, ℝ)}, ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
      (2 : ℝ)⁻¹ • (f + g) = u → f = g) : u * u = 1 := by
  let d : C(X, ℝ) := (2 : ℝ)⁻¹ • (1 - u * u)
  have hu_point (x : X) : |u x| ≤ 1 := by
    rw [← Real.norm_eq_abs, ← hu]
    exact ContinuousMap.norm_coe_le_norm u x
  have hplus : ‖u + d‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).2 fun x => by
    rw [Real.norm_eq_abs, abs_le]
    change -1 ≤ u x + (2 : ℝ)⁻¹ * (1 - u x * u x) ∧
      u x + (2 : ℝ)⁻¹ * (1 - u x * u x) ≤ 1
    obtain ⟨hl, hr⟩ := abs_le.mp (hu_point x)
    constructor <;> nlinarith [sq_nonneg (u x - 1), sq_nonneg (u x + 1)]
  have hminus : ‖u - d‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).2 fun x => by
    rw [Real.norm_eq_abs, abs_le]
    change -1 ≤ u x - (2 : ℝ)⁻¹ * (1 - u x * u x) ∧
      u x - (2 : ℝ)⁻¹ * (1 - u x * u x) ≤ 1
    obtain ⟨hl, hr⟩ := abs_le.mp (hu_point x)
    constructor <;> nlinarith [sq_nonneg (u x - 1), sq_nonneg (u x + 1)]
  have heq : u + d = u - d := hext hplus hminus (by
    ext x
    simp [d]
    ring)
  have hd : d = 0 := by
    ext x
    have hx := congrArg (fun k : C(X, ℝ) => k x) heq
    change u x + d x = u x - d x at hx
    change d x = 0
    linarith
  ext x
  have hx := congrArg (fun k : C(X, ℝ) => k x) hd
  change (2 : ℝ)⁻¹ * (1 - u x * u x) = 0 at hx
  change u x * u x = 1
  nlinarith

private lemma exists_continuousMap_of_unital_abs
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (T : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (hT1 : T 1 = 1)
    (hpos : ∀ (f : C(X, ℝ)), 0 ≤ f → 0 ≤ T f)
    (habs : ∀ f : C(X, ℝ), T |f| = |T f|) :
    ∃ φ : C(Y, X), ∀ (f : C(X, ℝ)) (y : Y), T f y = f (φ y) := by
  have hcommon (y : Y) :
      (⋂ f : {f : C(X, ℝ) // T f y = 0}, {x : X | f.1 x = 0}).Nonempty := by
    have h := isCompact_univ.inter_iInter_nonempty
      (fun f : {f : C(X, ℝ) // T f y = 0} => {x : X | f.1 x = 0})
      (fun f => isClosed_eq f.1.continuous continuous_const)
      (fun s => by
        let g : C(X, ℝ) := ∑ f ∈ s, |f.1|
        obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
          g.continuous.continuousOn
        refine ⟨x, Set.mem_inter (Set.mem_univ x) ?_⟩
        simp only [Set.mem_iInter]
        intro f hf
        by_contra hfx
        have hterm : |f.1 x| ≤ g x := by
          simpa [g] using Finset.single_le_sum (fun i _ => abs_nonneg (i.1 x)) hf
        have hgxpos : 0 < g x := (abs_pos.mpr hfx).trans_le hterm
        have hconst_le : (g x) • (1 : C(X, ℝ)) ≤ g := by
          intro z
          simpa using hx (Set.mem_univ z)
        have hnonneg : 0 ≤ T (g - (g x) • (1 : C(X, ℝ))) :=
          hpos _ (sub_nonneg.mpr hconst_le)
        have hTgy : T g y = 0 := by
          calc
            T g y = (∑ i ∈ s, T |i.1|) y := congrArg (fun q : C(Y, ℝ) => q y) (by
              dsimp [g]
              rw [map_sum])
            _ = (ContinuousMap.evalAlgHom ℝ ℝ y) (∑ i ∈ s, T |i.1|) := rfl
            _ = ∑ i ∈ s, (T |i.1|) y := map_sum _ _ _
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              rw [habs, ContinuousMap.abs_apply, i.property, abs_zero]
        have := hnonneg y
        rw [T.map_sub, T.map_smul, hT1] at this
        have hineq : (0 : ℝ) ≤ T g y - g x := by simpa using this
        rw [hTgy] at hineq
        linarith)
    simp only [Set.univ_inter] at h
    exact h
  let φ : Y → X := fun y => Classical.choose (hcommon y)
  have hφ_mem (y : Y) :
      φ y ∈ ⋂ f : {f : C(X, ℝ) // T f y = 0}, {x : X | f.1 x = 0} :=
    Classical.choose_spec (hcommon y)
  have hrepr (f : C(X, ℝ)) (y : Y) : T f y = f (φ y) := by
    let k : C(X, ℝ) := f - (T f y) • 1
    have hk : T k y = 0 := by
      dsimp [k]
      rw [T.map_sub, T.map_smul, hT1]
      simp
    have hkzero := Set.mem_iInter.mp (hφ_mem y) ⟨k, hk⟩
    change k (φ y) = 0 at hkzero
    dsimp [k] at hkzero
    simp only [mul_one] at hkzero
    linarith
  have hcontinuous : Continuous φ := by
    rw [continuous_iff_isClosed]
    intro s hs
    let I := {f : C(X, ℝ) | Set.EqOn f 0 s}
    have hpreimage : φ ⁻¹' s = ⋂ f : I, {y : Y | T f.1 y = 0} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hy f
        rw [hrepr]
        exact f.2 hy
      · intro hy
        by_contra hnot
        obtain ⟨f, hfs, hfone, -⟩ := exists_continuous_zero_one_of_isClosed hs
          (isClosed_singleton : IsClosed ({φ y} : Set X))
          (Set.disjoint_singleton_right.mpr hnot)
        have hz := hy ⟨f, hfs⟩
        rw [hrepr] at hz
        have hone := hfone (Set.mem_singleton (φ y))
        change f (φ y) = 1 at hone
        linarith
    rw [hpreimage]
    exact isClosed_iInter fun f => isClosed_eq (T f.1).continuous continuous_const
  exact ⟨⟨φ, hcontinuous⟩, hrepr⟩

private lemma eq_of_continuousMap_eq
    {X : Type*} [TopologicalSpace X] [NormalSpace X] [T1Space X]
    {x z : X} (h : ∀ f : C(X, ℝ), f x = f z) : x = z := by
  by_contra hxz
  obtain ⟨f, hfx, hfz, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({x} : Set X))
    (isClosed_singleton : IsClosed ({z} : Set X))
    (Set.disjoint_singleton.mpr hxz)
  have hx := hfx (Set.mem_singleton x)
  have hz := hfz (Set.mem_singleton z)
  have := h f
  change f x = 0 at hx
  change f z = 1 at hz
  linarith

private lemma homeomorph_of_unital_linearIsometryEquiv
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (T : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (hT1 : T 1 = 1) : Nonempty (X ≃ₜ Y) := by
  have hpos (f : C(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ T f := by
    have hshift : ‖f - ‖f‖ • (1 : C(X, ℝ))‖ ≤ ‖f‖ :=
      (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x => by
        rw [Real.norm_eq_abs, abs_le]
        have hbound : |f x| ≤ ‖f‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousMap.norm_coe_le_norm f x
        obtain ⟨_, hupper⟩ := abs_le.mp hbound
        have hnonneg := hf x
        change (0 : ℝ) ≤ f x at hnonneg
        constructor
        · simpa using (show -‖f‖ ≤ f x - ‖f‖ by linarith)
        · simpa using (show f x - ‖f‖ ≤ ‖f‖ by linarith)
    have hTshift : ‖T f - ‖f‖ • (1 : C(Y, ℝ))‖ ≤ ‖f‖ := by
      rw [← hT1, ← T.map_smul, ← T.map_sub, T.norm_map]
      exact hshift
    intro y
    have hy := (ContinuousMap.norm_coe_le_norm
      (T f - ‖f‖ • (1 : C(Y, ℝ))) y).trans hTshift
    rw [Real.norm_eq_abs, abs_le] at hy
    have hylower : -‖f‖ ≤ T f y - ‖f‖ := by simpa using hy.1
    change (0 : ℝ) ≤ T f y
    linarith
  have hTinv1 : T.symm 1 = 1 := by
    apply T.injective
    simp [hT1]
  have hpos_inv (g : C(Y, ℝ)) (hg : 0 ≤ g) : 0 ≤ T.symm g := by
    have hshift : ‖g - ‖g‖ • (1 : C(Y, ℝ))‖ ≤ ‖g‖ :=
      (ContinuousMap.norm_le _ (norm_nonneg g)).2 fun y => by
        rw [Real.norm_eq_abs, abs_le]
        have hbound : |g y| ≤ ‖g‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousMap.norm_coe_le_norm g y
        obtain ⟨_, hupper⟩ := abs_le.mp hbound
        have hnonneg := hg y
        change (0 : ℝ) ≤ g y at hnonneg
        constructor
        · simpa using (show -‖g‖ ≤ g y - ‖g‖ by linarith)
        · simpa using (show g y - ‖g‖ ≤ ‖g‖ by linarith)
    have hTshift : ‖T.symm g - ‖g‖ • (1 : C(X, ℝ))‖ ≤ ‖g‖ := by
      rw [← hTinv1, ← T.symm.map_smul, ← T.symm.map_sub, T.symm.norm_map]
      exact hshift
    intro x
    have hx := (ContinuousMap.norm_coe_le_norm
      (T.symm g - ‖g‖ • (1 : C(X, ℝ))) x).trans hTshift
    rw [Real.norm_eq_abs, abs_le] at hx
    have hxlower : -‖g‖ ≤ T.symm g x - ‖g‖ := by simpa using hx.1
    change (0 : ℝ) ≤ T.symm g x
    linarith
  have hle (f g : C(X, ℝ)) : T f ≤ T g ↔ f ≤ g := by
    constructor
    · intro h
      have := hpos_inv (T g - T f) (sub_nonneg.mpr h)
      simpa using this
    · intro h
      have := hpos (g - f) (sub_nonneg.mpr h)
      simpa using this
  have hle_inv (f g : C(Y, ℝ)) : T.symm f ≤ T.symm g ↔ f ≤ g := by
    constructor
    · intro h
      simpa using (hle (T.symm f) (T.symm g)).mpr h
    · intro h
      exact (hle (T.symm f) (T.symm g)).mp (by simpa using h)
  have habs (f : C(X, ℝ)) : T |f| = |T f| := by
    apply le_antisymm
    · have hpre : |f| ≤ T.symm |T f| := by
        have hneg : T.symm (-|T f|) ≤ T.symm (T f) :=
          (hle_inv (-|T f|) (T f)).2 (by
            intro y
            simpa using neg_abs_le (T f y))
        have hself : T.symm (T f) ≤ T.symm |T f| :=
          (hle_inv (T f) |T f|).2 (by
            intro y
            exact le_abs_self (T f y))
        intro x
        apply abs_le.mpr
        constructor
        · simpa using hneg x
        · simpa using hself x
      simpa using (hle |f| (T.symm |T f|)).2 hpre
    · intro y
      apply abs_le.mpr
      constructor
      · simpa using (hle (-|f|) f).2 (by
          intro x
          simpa using neg_abs_le (f x)) y
      · exact (hle f |f|).2 (by
          intro x
          exact le_abs_self (f x)) y
  have habs_inv (g : C(Y, ℝ)) : T.symm |g| = |T.symm g| := by
    apply T.injective
    rw [habs]
    simp
  obtain ⟨φ, hφ⟩ := exists_continuousMap_of_unital_abs T hT1 hpos habs
  obtain ⟨ψ, hψ⟩ := exists_continuousMap_of_unital_abs T.symm hTinv1 hpos_inv habs_inv
  let equiv : X ≃ Y :=
    { toFun := ψ
      invFun := φ
      left_inv := fun x => eq_of_continuousMap_eq fun f => by
        rw [← hφ f (ψ x), ← hψ (T f) x]
        simp
      right_inv := fun y => eq_of_continuousMap_eq fun g => by
        rw [← hψ g (φ y), ← hφ (T.symm g) y]
        simp }
  exact ⟨
    { toEquiv := equiv
      continuous_toFun := ψ.continuous
      continuous_invFun := φ.continuous }⟩

/--
**Banach–Stone theorem for real scalars.** Let $X$ and $Y$ be compact Hausdorff spaces, and let
$C(X, \mathbb{R})$ and $C(Y, \mathbb{R})$ be the real Banach spaces of continuous real functions
on them with the supremum norm. If there is a surjective linear isometry from $C(X, \mathbb{R})$
onto $C(Y, \mathbb{R})$, then $X$ and $Y$ are homeomorphic.

Proves `Wanted` entry `banachStone_real`.

Source: S. Banach, Theorie des
operations lineaires, 1932 and M. Stone, Trans. Amer. Math. Soc. 41 (1937) 375-381; textbook
Semadeni, Banach Spaces of Continuous Functions, 1971; Lean states compact Hausdorff case with
Banach-space linear isometric isomorphism implies homeomorphism, real coefficient field
specialization.
-/
theorem banachStone_real
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) : Nonempty (X ≃ₜ Y) := by
  classical
  by_cases hX : Nonempty X
  · let _ : Nonempty X := hX
    have hY : Nonempty Y := by
      by_contra hY
      let _ : IsEmpty Y := not_nonempty_iff.mp hY
      have hzero_one : (0 : C(X, ℝ)) = 1 :=
        e.injective (Subsingleton.elim (e 0) (e 1))
      let x : X := Classical.choice hX
      have hx := congrArg (fun f : C(X, ℝ) => f x) hzero_one
      norm_num at hx
    let _ : Nonempty Y := hY
    let u : C(Y, ℝ) := e 1
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [e.norm_map, norm_one]
    have hext : ∀ {f g : C(Y, ℝ)}, ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
        (2 : ℝ)⁻¹ • (f + g) = u → f = g := by
      intro f g hf hg hfg
      apply e.symm.injective
      apply one_midpoint_unique
      · simpa using hf
      · simpa using hg
      · apply e.injective
        rw [e.map_smul, e.map_add]
        simp only [e.apply_symm_apply]
        simpa [u] using hfg
    have hu_sq : u * u = 1 := square_eq_one_of_midpoint_unique u hu hext
    have hu_abs (y : Y) : |u y| = 1 := by
      have hy := congrArg (fun f : C(Y, ℝ) => f y) hu_sq
      change u y * u y = 1 at hy
      have habssq : |u y| * |u y| = 1 := by
        rw [← abs_mul, hy, abs_one]
      nlinarith [abs_nonneg (u y)]
    let T : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ) :=
      { toFun := fun f => u * e f
        invFun := fun g => e.symm (u * g)
        left_inv := fun f => by
          apply e.injective
          simp only [e.apply_symm_apply]
          rw [← mul_assoc, hu_sq, one_mul]
        right_inv := fun g => by
          simp only [e.apply_symm_apply]
          rw [← mul_assoc, hu_sq, one_mul]
        map_add' := fun f g => by
          simp only [map_add]
          ring
        map_smul' := fun r f => by
          simp only [map_smul]
          ext y
          change u y * (r * e f y) = r * (u y * e f y)
          ring
        norm_map' := fun f => by
          calc
            ‖u * e f‖ = ‖e f‖ := by
              rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
              congr with y
              change ‖u y * e f y‖ = ‖e f y‖
              rw [norm_mul, Real.norm_eq_abs, hu_abs, one_mul]
            _ = ‖f‖ := e.norm_map f }
    apply homeomorph_of_unital_linearIsometryEquiv T
    dsimp [T]
    exact hu_sq
  · let _ : IsEmpty X := not_nonempty_iff.mp hX
    have hY : IsEmpty Y := by
      rw [← not_nonempty_iff]
      intro hY
      let _ : Nonempty Y := hY
      have hzero_one : (0 : C(Y, ℝ)) = 1 :=
        e.symm.injective (Subsingleton.elim (e.symm 0) (e.symm 1))
      let y : Y := Classical.choice hY
      have hy := congrArg (fun f : C(Y, ℝ) => f y) hzero_one
      norm_num at hy
    let _ : IsEmpty Y := hY
    let equiv := Equiv.equivOfIsEmpty X Y
    exact ⟨
      { toEquiv := equiv
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }⟩

end MathlibExt.Analysis.FunctionalAnalysis.BanachStoneWanted
