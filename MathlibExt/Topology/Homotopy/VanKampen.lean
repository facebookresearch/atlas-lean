/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
-- Original contributors: Adam Kiezun, Muse Spark 1.3.
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import MathlibExt.Topology.Homotopy.PathOpenCoverGrid

@[expose] public section

/-!
# Seifert–van Kampen theorem — fundamental groupoid pushout

For open `U, V` covering `X`, `π₁(X)` is the pushout of `π₁(U)` and `π₁(V)`
over `π₁(U ∩ V)` in groupoids.
-/

open CategoryTheory Topology
open scoped FundamentalGroupoid

namespace MathlibExt.Topology.Homotopy.VanKampenWanted

/-- Inclusion of `↥U` into `X` via `Subtype.val`. -/
noncomputable def inclusionSub {X : Type*} [TopologicalSpace X] (U : Set X) :
    C(↥U, X) where
  toFun x := x.val
  continuous_toFun := continuous_subtype_val

/-- Inclusion `U ∩ V → U` as a bundled continuous map. -/
noncomputable def inclusionInterLeft {X : Type*} [TopologicalSpace X]
    (U V : Set X) : C(↥(U ∩ V), ↥U) :=
  ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)

/-- Inclusion `U ∩ V → V` as a bundled continuous map. -/
noncomputable def inclusionInterRight {X : Type*} [TopologicalSpace X]
    (U V : Set X) : C(↥(U ∩ V), ↥V) :=
  ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)

/-- The inclusion square commutes: both composites are `π` of the inclusion
`U ∩ V → X`. -/
private theorem vk_square_comm {X : Type*} [TopologicalSpace X] {U V : Set X} :
    (FundamentalGroupoid.map (inclusionInterLeft U V) ⋙
        FundamentalGroupoid.map (inclusionSub (X := X) U) =
      FundamentalGroupoid.map (inclusionInterRight U V) ⋙
        FundamentalGroupoid.map (inclusionSub (X := X) V)) := by
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  rfl

/-- Bottom edge of the unit square, from `(0, 0)` to `(1, 0)`. -/
private def vkEB : Path ((0, 0) : ↥unitInterval × ↥unitInterval) (1, 0) where
  toFun u := (u, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- Right edge of the unit square, from `(1, 0)` to `(1, 1)`. -/
private def vkER : Path ((1, 0) : ↥unitInterval × ↥unitInterval) (1, 1) where
  toFun v := (1, v)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- Left edge of the unit square, from `(0, 0)` to `(0, 1)`. -/
private def vkEL : Path ((0, 0) : ↥unitInterval × ↥unitInterval) (0, 1) where
  toFun v := (0, v)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- Top edge of the unit square, from `(0, 1)` to `(1, 1)`. -/
private def vkET : Path ((0, 1) : ↥unitInterval × ↥unitInterval) (1, 1) where
  toFun u := (u, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private theorem vkEB_apply (t : ↥unitInterval) : ⇑vkEB t = (t, 0) := rfl

private theorem vkER_apply (t : ↥unitInterval) : ⇑vkER t = (1, t) := rfl

private theorem vkEL_apply (t : ↥unitInterval) : ⇑vkEL t = (0, t) := rfl

private theorem vkET_apply (t : ↥unitInterval) : ⇑vkET t = (t, 1) := rfl

/-- Corner-square lemma: the two corner paths around the boundary of a square
have equal homotopy classes. The square `I × I` is contractible, hence simply
connected; push the homotopy forward along `g`. -/
private theorem vk_corner_square {Y : Type*} [TopologicalSpace Y]
    (g : C(↥unitInterval × ↥unitInterval, Y))
    {y00 y10 y01 y11 : Y}
    (bot : Path y00 y10) (rgt : Path y10 y11)
    (lft : Path y00 y01) (top : Path y01 y11)
    (hbot : ∀ u : ↥unitInterval, bot u = g (u, 0))
    (hrgt : ∀ v : ↥unitInterval, rgt v = g (1, v))
    (hlft : ∀ v : ↥unitInterval, lft v = g (0, v))
    (htop : ∀ u : ↥unitInterval, top u = g (u, 1)) :
    (Path.Homotopic.Quotient.mk bot).trans (Path.Homotopic.Quotient.mk rgt) =
      (Path.Homotopic.Quotient.mk lft).trans (Path.Homotopic.Quotient.mk top) := by
  have e00 : y00 = g (0, 0) := bot.source.symm.trans (hbot 0)
  have e10 : y10 = g (1, 0) := bot.target.symm.trans (hbot 1)
  have e01 : y01 = g (0, 1) := lft.target.symm.trans (hlft 1)
  have e11 : y11 = g (1, 1) := rgt.target.symm.trans (hrgt 1)
  subst e00
  subst e10
  subst e01
  subst e11
  have : ContractibleSpace ↥unitInterval :=
    Convex.contractibleSpace (convex_Icc (0 : ℝ) 1)
      ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩
  have : SimplyConnectedSpace (↥unitInterval × ↥unitInterval) :=
    SimplyConnectedSpace.ofContractible _
  have hhom : (vkEB.trans vkER).Homotopic (vkEL.trans vkET) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hmap := hhom.map g
  have h1 : (vkEB.trans vkER).map g.continuous = bot.trans rgt := by
    rw [Path.map_trans]
    congr 1
    · ext t
      simp only [Path.map_coe, Function.comp_apply, vkEB_apply]
      exact (hbot t).symm
    · ext t
      simp only [Path.map_coe, Function.comp_apply, vkER_apply]
      exact (hrgt t).symm
  have h2 : (vkEL.trans vkET).map g.continuous = lft.trans top := by
    rw [Path.map_trans]
    congr 1
    · ext t
      simp only [Path.map_coe, Function.comp_apply, vkEL_apply]
      exact (hlft t).symm
    · ext t
      simp only [Path.map_coe, Function.comp_apply, vkET_apply]
      exact (htop t).symm
  rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans,
    ← h1, ← h2]
  exact Path.Homotopic.Quotient.eq.mpr hmap

/-- Private compatibility name for the canonical public uniform grid. -/
private noncomputable abbrev vkGrid (N k : ℕ) : ↥unitInterval :=
  unitInterval.uniformGrid N k

/-- Coercion of a grid point, unfolding the projection. -/
private theorem vkGrid_coe (N k : ℕ) :
    ((vkGrid N k : ↥unitInterval) : ℝ) =
      ((Set.projIcc 0 1 zero_le_one (((k : ℕ) : ℝ) / (N : ℝ)) :
        ↥unitInterval) : ℝ) :=
  unitInterval.uniformGrid_coe N k

/-- A path is small if its range lies in `U` or in `V`. -/
private def vkSmall {X : Type*} [TopologicalSpace X] (U V : Set X)
    {a b : X} (p : Path a b) : Prop :=
  Set.range ⇑p ⊆ U ∨ Set.range ⇑p ⊆ V

/-- Admissibility: every grid piece of `γ` at level `N` is small. -/
private def vkAdm {X : Type*} [TopologicalSpace X] (U V : Set X)
    {a b : X} (γ : Path a b) (N : ℕ) : Prop :=
  ∀ k, vkSmall U V (γ.subpath (vkGrid N k) (vkGrid N (k + 1)))

/-- Membership transport, hiding the subset-proof application so that rewrite
matching never sees it. -/
private theorem vkMem_of_subset {X : Type*} {s t : Set X} {x : X}
    (h : s ⊆ t) (hm : x ∈ s) : x ∈ t :=
  h hm

private theorem vkGrid_zero (N : ℕ) : vkGrid N 0 = 0 := by
  exact unitInterval.uniformGrid_zero N

private theorem vkGrid_top {N k : ℕ} (hN : 1 ≤ N) (hk : N ≤ k) :
    vkGrid N k = 1 := by
  exact unitInterval.uniformGrid_top hN hk

private theorem vkGrid_mono (N : ℕ) : Monotone (vkGrid N) := by
  exact unitInterval.uniformGrid_monotone N

private theorem vkGrid_gap (N k : ℕ) :
    ((vkGrid N (k + 1) : ↥unitInterval) : ℝ) - (vkGrid N k : ℝ) ≤
      1 / (N : ℝ) := by
  exact unitInterval.uniformGrid_gap N k

/-- Inside `[0, 1]` the projection is the identity. -/
private theorem vkGrid_val_of_le {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    ((vkGrid N k : ↥unitInterval) : ℝ) = (k : ℝ) / (N : ℝ) := by
  exact unitInterval.uniformGrid_val_of_le hN hk

/-- Block structure: the `(N * M)`-grid point `j * M` is the `N`-grid point `j`. -/
private theorem vkGrid_block_eq {N M j : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hj : j ≤ N) : vkGrid (N * M) (j * M) = vkGrid N j := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hMr : (M : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hMpos)
  have h1 : 1 ≤ N * M := by
    calc (1 : ℕ) = 1 * 1 := by ring
    _ ≤ N * M := Nat.mul_le_mul hN hM
  have h2 : j * M ≤ N * M := Nat.mul_le_mul hj (le_refl M)
  apply Subtype.ext
  rw [vkGrid_val_of_le h1 h2, vkGrid_val_of_le hN hj]
  push_cast
  exact mul_div_mul_right _ _ hMr

/-- Doubling, first half: twice the `(2 * N)`-grid value is the `N`-grid value. -/
private theorem vkGrid_double_fst {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    2 * ((vkGrid (2 * N) k : ↥unitInterval) : ℝ) =
      ((vkGrid N k : ↥unitInterval) : ℝ) := by
  have h2N : 1 ≤ 2 * N := by omega
  have hk2 : k ≤ 2 * N := by omega
  rw [vkGrid_val_of_le h2N hk2, vkGrid_val_of_le hN hk]
  push_cast
  have hNr : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have h2Nr : (2 : ℝ) * (N : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hNr
  field_simp

/-- Doubling, second half. -/
private theorem vkGrid_double_snd {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    2 * ((vkGrid (2 * N) (N + k) : ↥unitInterval) : ℝ) - 1 =
      ((vkGrid N k : ↥unitInterval) : ℝ) := by
  have h2N : 1 ≤ 2 * N := by omega
  have hk2 : N + k ≤ 2 * N := by omega
  rw [vkGrid_val_of_le h2N hk2, vkGrid_val_of_le hN hk]
  push_cast
  have hNr : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have h2Nr : (2 : ℝ) * (N : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hNr
  field_simp
  ring

/-- Grid comparison through natural division: the `(N * M)`-grid cells lie
between consecutive `N`-grid points. -/
private theorem vkGrid_div_bounds {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (k : ℕ) :
    ((vkGrid N (k / M) : ↥unitInterval) : ℝ) ≤
      ((vkGrid (N * M) k : ↥unitInterval) : ℝ) ∧
    ((vkGrid (N * M) (k + 1) : ↥unitInterval) : ℝ) ≤
      ((vkGrid N (k / M + 1) : ↥unitInterval) : ℝ) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hN' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNM' : (0 : ℝ) < (((N * M : ℕ)) : ℝ) := by
    have : 1 ≤ N * M := by
      calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ N * M := Nat.mul_le_mul hN hM
    exact Nat.cast_pos.mpr this
  have hdm := Nat.div_add_mod k M
  have hmod : k % M < M := Nat.mod_lt k hMpos
  have e0 : k / M * M = M * (k / M) := by ring
  have e1 : (k / M + 1) * M = M * (k / M) + M := by ring
  have hlo0 : k / M * M ≤ k := by omega
  have hhi0 : k + 1 ≤ (k / M + 1) * M := by omega
  constructor
  · have hfrac : ((((k / M : ℕ)) : ℝ) / (N : ℝ)) ≤
        ((k : ℝ) / (((N * M : ℕ)) : ℝ)) := by
      rw [div_le_div_iff₀ hN' hNM']
      have hcast : ((((k / M * M : ℕ)) : ℝ)) ≤ (k : ℝ) := by
        exact_mod_cast hlo0
      have hmul := mul_le_mul_of_nonneg_right hcast (Nat.cast_nonneg N)
      push_cast at hmul ⊢
      linear_combination hmul
    exact Set.monotone_projIcc (a := (0 : ℝ)) (b := 1) zero_le_one hfrac
  · have hfrac : ((((k + 1 : ℕ)) : ℝ) / (((N * M : ℕ)) : ℝ)) ≤
        ((((k / M + 1 : ℕ)) : ℝ) / (N : ℝ)) := by
      rw [div_le_div_iff₀ hNM' hN']
      have hcast : ((((k + 1 : ℕ)) : ℝ)) ≤ ((((k / M + 1) * M : ℕ)) : ℝ) := by
        exact_mod_cast hhi0
      have hmul := mul_le_mul_of_nonneg_right hcast (Nat.cast_nonneg N)
      push_cast at hmul ⊢
      linear_combination hmul
    exact Set.monotone_projIcc (a := (0 : ℝ)) (b := 1) zero_le_one hfrac

/-- Admissibility refines: an `N`-admissible grid is `(N * M)`-admissible. -/
private theorem vkAdm_mul {X : Type*} [TopologicalSpace X] {U V : Set X}
    {a b : X} {γ : Path a b} {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hA : vkAdm U V γ N) :
    vkAdm U V γ (N * M) := by
  unfold vkAdm
  intro k
  have hb := vkGrid_div_bounds hN hM k
  have hsub : Set.uIcc (vkGrid (N * M) k) (vkGrid (N * M) (k + 1)) ⊆
      Set.uIcc (vkGrid N (k / M)) (vkGrid N (k / M + 1)) := by
    rw [Set.uIcc_of_le (vkGrid_mono _ (Nat.le_succ k)),
      Set.uIcc_of_le (vkGrid_mono _ (Nat.le_succ _))]
    exact Set.Icc_subset_Icc (by exact_mod_cast hb.1) (by exact_mod_cast hb.2)
  rcases hA (k / M) with hU | hV
  · left
    simp only [Path.range_subpath] at hU ⊢
    intro x hx
    apply hU
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨t, hsub ht, rfl⟩
  · right
    simp only [Path.range_subpath] at hV ⊢
    intro x hx
    apply hV
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨t, hsub ht, rfl⟩

/-- Object map: `F_U` on `U`, else `F_V` on `V`. -/
private noncomputable def vkObj0 {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G) (hCover : U ∪ V = Set.univ)
    (x : X) : G := by
  classical
  exact if h : x ∈ U then F_U.obj ⟨x, h⟩
    else F_V.obj ⟨x, by
      have hxU : x ∈ U ∪ V := by rw [hCover]; exact Set.mem_univ x
      have hor : x ∈ U ∨ x ∈ V := hxU
      exact hor.resolve_left h⟩

private theorem vkObj0_eq_U {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G) (hCover : U ∪ V = Set.univ)
    {x : X} (hx : x ∈ U) : vkObj0 F_U F_V hCover x = F_U.obj ⟨x, hx⟩ := by
  unfold vkObj0
  rw [dite_eq_left hx]

private theorem vkObj0_eq_V {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {x : X} (hx : x ∈ V) : vkObj0 F_U F_V hCover x = F_V.obj ⟨x, hx⟩ := by
  by_cases hUx : x ∈ U
  · rw [vkObj0_eq_U F_U F_V hCover hUx]
    have hobj := Functor.congr_obj hCompat
      (⟨x, hUx, hx⟩ : FundamentalGroupoid ↥(U ∩ V))
    have eL : ((FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U).obj
        (⟨x, hUx, hx⟩ : FundamentalGroupoid ↥(U ∩ V)) = F_U.obj ⟨x, hUx⟩ :=
      rfl
    have eR : ((FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V).obj
        (⟨x, hUx, hx⟩ : FundamentalGroupoid ↥(U ∩ V)) = F_V.obj ⟨x, hx⟩ :=
      rfl
    rw [eL, eR] at hobj
    exact hobj
  · unfold vkObj0
    rw [dite_eq_right hUx]

/-- View a path in `X` with range in `W` as a path in `↥W`. -/
private noncomputable def vkRes {X : Type*} [TopologicalSpace X] (W : Set X)
    {a b : X} (p : Path a b) (h : Set.range ⇑p ⊆ W) :
    Path (⟨a, h ⟨0, p.source⟩⟩ : ↥W) (⟨b, h ⟨1, p.target⟩⟩ : ↥W) where
  toFun t := ⟨p t, h ⟨t, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk p.continuous (fun t => h ⟨t, rfl⟩)
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- Local value in the `U` chart, conjugated to `vkObj0` endpoints. -/
private noncomputable def vkLU {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G) (hCover : U ∪ V = Set.univ)
    {a b : X} (p : Path a b) (h : Set.range ⇑p ⊆ U) :
    vkObj0 F_U F_V hCover a ⟶ vkObj0 F_U F_V hCover b :=
  eqToHom (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset h ⟨0, p.source⟩)) ≫
    F_U.map (Path.Homotopic.Quotient.mk (vkRes U p h)) ≫
      eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset h ⟨1, p.target⟩)).symm

/-- Local value in the `V` chart, conjugated to `vkObj0` endpoints. -/
private noncomputable def vkLV {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (p : Path a b) (h : Set.range ⇑p ⊆ V) :
    vkObj0 F_U F_V hCover a ⟶ vkObj0 F_U F_V hCover b :=
  eqToHom (vkObj0_eq_V F_U F_V hCompat hCover (vkMem_of_subset h ⟨0, p.source⟩)) ≫
    F_V.map (Path.Homotopic.Quotient.mk (vkRes V p h)) ≫
      eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
        (vkMem_of_subset h ⟨1, p.target⟩)).symm

/-- Any two `eqToHom`s between the same objects agree. -/
private theorem vkEqToHom_eq {C : Type*} [Category C] {X Y : C} (p q : X = Y) :
    eqToHom p = eqToHom q := by
  subst p
  rfl

/-- Compatibility: on paths lying in `U ∩ V`, the two local values agree. -/
private theorem vkCompat {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (p : Path a b) (h : Set.range ⇑p ⊆ U ∩ V) :
    vkLU F_U F_V hCover p (h.trans Set.inter_subset_left) =
      vkLV F_U F_V hCompat hCover p (h.trans Set.inter_subset_right) := by
  have hc := CategoryTheory.Functor.congr_hom hCompat
    (Path.Homotopic.Quotient.mk (vkRes (U ∩ V) p h))
  have peL : (vkRes (U ∩ V) p h).map
      (inclusionInterLeft U V).continuous =
      vkRes U p (h.trans Set.inter_subset_left) := by
    apply Path.ext
    rfl
  have peR : (vkRes (U ∩ V) p h).map
      (inclusionInterRight U V).continuous =
      vkRes V p (h.trans Set.inter_subset_right) := by
    apply Path.ext
    rfl
  have qL : Path.Homotopic.Quotient.mk
      (vkRes U p (h.trans Set.inter_subset_left)) =
      (Path.Homotopic.Quotient.mk (vkRes (U ∩ V) p h)).map
        (inclusionInterLeft U V) :=
    (congrArg Path.Homotopic.Quotient.mk peL).symm.trans
      (Path.Homotopic.Quotient.mk_map _ _)
  have qR : Path.Homotopic.Quotient.mk
      (vkRes V p (h.trans Set.inter_subset_right)) =
      (Path.Homotopic.Quotient.mk (vkRes (U ∩ V) p h)).map
        (inclusionInterRight U V) :=
    (congrArg Path.Homotopic.Quotient.mk peR).symm.trans
      (Path.Homotopic.Quotient.mk_map _ _)
  have eL : F_U.map (Path.Homotopic.Quotient.mk
      (vkRes U p (h.trans Set.inter_subset_left))) =
      ((FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U).map
        (Path.Homotopic.Quotient.mk (vkRes (U ∩ V) p h)) :=
    (congrArg F_U.map qL).trans rfl
  have eR : F_V.map (Path.Homotopic.Quotient.mk
      (vkRes V p (h.trans Set.inter_subset_right))) =
      ((FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V).map
        (Path.Homotopic.Quotient.mk (vkRes (U ∩ V) p h)) :=
    (congrArg F_V.map qR).trans rfl
  have hcGround : F_U.map (Path.Homotopic.Quotient.mk
      (vkRes U p (h.trans Set.inter_subset_left))) =
      eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨a, h ⟨0, p.source⟩⟩ : ↥(U ∩ V)))) ≫
        F_V.map (Path.Homotopic.Quotient.mk
          (vkRes V p (h.trans Set.inter_subset_right))) ≫
        eqToHom (CategoryTheory.Functor.congr_obj hCompat
          (FundamentalGroupoid.mk (⟨b, h ⟨1, p.target⟩⟩ : ↥(U ∩ V)))).symm := by
    cases eL
    cases eR
    exact hc
  have hL : eqToHom (vkObj0_eq_U F_U F_V hCover
      (vkMem_of_subset (h.trans Set.inter_subset_left) ⟨0, p.source⟩)) ≫
      eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨a, h ⟨0, p.source⟩⟩ : ↥(U ∩ V)))) =
      eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
        (vkMem_of_subset (h.trans Set.inter_subset_right) ⟨0, p.source⟩)) :=
    (CategoryTheory.eqToHom_trans _ _).trans (vkEqToHom_eq _ _)
  have hR : eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨b, h ⟨1, p.target⟩⟩ : ↥(U ∩ V)))).symm ≫
      eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset (h.trans Set.inter_subset_left) ⟨1, p.target⟩)).symm =
      eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
        (vkMem_of_subset (h.trans Set.inter_subset_right) ⟨1, p.target⟩)).symm :=
    (CategoryTheory.eqToHom_trans _ _).trans (vkEqToHom_eq _ _)
  change eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset (h.trans Set.inter_subset_left) ⟨0, p.source⟩)) ≫
        F_U.map (Path.Homotopic.Quotient.mk
          (vkRes U p (h.trans Set.inter_subset_left))) ≫
        eqToHom (vkObj0_eq_U F_U F_V hCover
          (vkMem_of_subset (h.trans Set.inter_subset_left)
            ⟨1, p.target⟩)).symm =
      eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
        (vkMem_of_subset (h.trans Set.inter_subset_right) ⟨0, p.source⟩)) ≫
        F_V.map (Path.Homotopic.Quotient.mk
          (vkRes V p (h.trans Set.inter_subset_right))) ≫
        eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
          (vkMem_of_subset (h.trans Set.inter_subset_right)
            ⟨1, p.target⟩)).symm
  rw [hcGround]
  have step1 : (eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset (h.trans Set.inter_subset_left) ⟨0, p.source⟩)) ≫
      eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨a, h ⟨0, p.source⟩⟩ : ↥(U ∩ V))))) ≫
      F_V.map (Path.Homotopic.Quotient.mk
        (vkRes V p (h.trans Set.inter_subset_right))) ≫
      (eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨b, h ⟨1, p.target⟩⟩ : ↥(U ∩ V)))).symm ≫
      eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset (h.trans Set.inter_subset_left)
          ⟨1, p.target⟩)).symm) =
      eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
        (vkMem_of_subset (h.trans Set.inter_subset_right) ⟨0, p.source⟩)) ≫
      F_V.map (Path.Homotopic.Quotient.mk
        (vkRes V p (h.trans Set.inter_subset_right))) ≫
      eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
        (vkMem_of_subset (h.trans Set.inter_subset_right)
          ⟨1, p.target⟩)).symm := by
    calc (eqToHom (vkObj0_eq_U F_U F_V hCover
          (vkMem_of_subset (h.trans Set.inter_subset_left) ⟨0, p.source⟩)) ≫
        eqToHom (CategoryTheory.Functor.congr_obj hCompat
          (FundamentalGroupoid.mk (⟨a, h ⟨0, p.source⟩⟩ : ↥(U ∩ V))))) ≫
        F_V.map (Path.Homotopic.Quotient.mk
          (vkRes V p (h.trans Set.inter_subset_right))) ≫
        (eqToHom (CategoryTheory.Functor.congr_obj hCompat
          (FundamentalGroupoid.mk (⟨b, h ⟨1, p.target⟩⟩ : ↥(U ∩ V)))).symm ≫
        eqToHom (vkObj0_eq_U F_U F_V hCover
          (vkMem_of_subset (h.trans Set.inter_subset_left)
            ⟨1, p.target⟩)).symm)
        = eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
          (vkMem_of_subset (h.trans Set.inter_subset_right) ⟨0, p.source⟩)) ≫
        F_V.map (Path.Homotopic.Quotient.mk
          (vkRes V p (h.trans Set.inter_subset_right))) ≫
        (eqToHom (CategoryTheory.Functor.congr_obj hCompat
          (FundamentalGroupoid.mk (⟨b, h ⟨1, p.target⟩⟩ : ↥(U ∩ V)))).symm ≫
        eqToHom (vkObj0_eq_U F_U F_V hCover
          (vkMem_of_subset (h.trans Set.inter_subset_left)
            ⟨1, p.target⟩)).symm) :=
          congrArg (· ≫ _ ≫ _) hL
      _ = eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
          (vkMem_of_subset (h.trans Set.inter_subset_right) ⟨0, p.source⟩)) ≫
        F_V.map (Path.Homotopic.Quotient.mk
          (vkRes V p (h.trans Set.inter_subset_right))) ≫
        eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
          (vkMem_of_subset (h.trans Set.inter_subset_right)
            ⟨1, p.target⟩)).symm :=
          congrArg (_ ≫ _ ≫ ·) hR
  calc eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset (h.trans Set.inter_subset_left) ⟨0, p.source⟩)) ≫
      (eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨a, h ⟨0, p.source⟩⟩ : ↥(U ∩ V)))) ≫
      F_V.map (Path.Homotopic.Quotient.mk
        (vkRes V p (h.trans Set.inter_subset_right))) ≫
      eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨b, h ⟨1, p.target⟩⟩ : ↥(U ∩ V)))).symm) ≫
      eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset (h.trans Set.inter_subset_left)
          ⟨1, p.target⟩)).symm
      = (eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset (h.trans Set.inter_subset_left) ⟨0, p.source⟩)) ≫
      eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨a, h ⟨0, p.source⟩⟩ : ↥(U ∩ V))))) ≫
      F_V.map (Path.Homotopic.Quotient.mk
        (vkRes V p (h.trans Set.inter_subset_right))) ≫
      (eqToHom (CategoryTheory.Functor.congr_obj hCompat
        (FundamentalGroupoid.mk (⟨b, h ⟨1, p.target⟩⟩ : ↥(U ∩ V)))).symm ≫
      eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset (h.trans Set.inter_subset_left)
          ⟨1, p.target⟩)).symm) := by
        simp only [Category.assoc]
    _ = _ := step1

/-- Local value on a small path: `U` chart if possible, else `V`. -/
private noncomputable def vkLoc {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (p : Path a b) (hs : vkSmall U V p) :
    vkObj0 F_U F_V hCover a ⟶ vkObj0 F_U F_V hCover b := by
  classical
  exact if hU' : Set.range ⇑p ⊆ U then vkLU F_U F_V hCover p hU'
    else vkLV F_U F_V hCompat hCover p (hs.resolve_left hU')

private theorem vkLoc_of_mem_U {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (p : Path a b) (hs : vkSmall U V p)
    (h : Set.range ⇑p ⊆ U) :
    vkLoc F_U F_V hCompat hCover p hs = vkLU F_U F_V hCover p h := by
  unfold vkLoc
  rw [dite_eq_left h]

private theorem vkLoc_of_mem_V {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (p : Path a b) (hs : vkSmall U V p)
    (h : Set.range ⇑p ⊆ V) (hn : ¬ Set.range ⇑p ⊆ U) :
    vkLoc F_U F_V hCompat hCover p hs = vkLV F_U F_V hCompat hCover p h := by
  unfold vkLoc
  rw [dite_eq_right hn]

/-- `loc` equals `lV` whenever the range lies in `V` (uses `vkCompat` on overlap). -/
private theorem vkLoc_eq_lV {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} {p : Path a b} (hs : vkSmall U V p)
    (h : Set.range ⇑p ⊆ V) :
    vkLoc F_U F_V hCompat hCover p hs =
      vkLV F_U F_V hCompat hCover p h := by
  by_cases hU : Set.range ⇑p ⊆ U
  · have hUV : Set.range ⇑p ⊆ U ∩ V := Set.subset_inter hU h
    have h1 : vkLoc F_U F_V hCompat hCover p hs =
        vkLU F_U F_V hCover p hU :=
      vkLoc_of_mem_U F_U F_V hCompat hCover p hs hU
    have hc := vkCompat F_U F_V hCompat hCover p hUV
    have eU : vkLU F_U F_V hCover p hU =
        vkLU F_U F_V hCover p (hUV.trans Set.inter_subset_left) := rfl
    have eV : vkLV F_U F_V hCompat hCover p h =
        vkLV F_U F_V hCompat hCover p (hUV.trans Set.inter_subset_right) := rfl
    rw [h1, eU, hc, ← eV]
  · exact vkLoc_of_mem_V F_U F_V hCompat hCover p hs h hU

/-- Pointwise-equal small paths have conjugate local values. -/
private theorem vkLoc_congr {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b a' b' : X} {p : Path a b} {q : Path a' b'}
    (hs : vkSmall U V p) (hs' : vkSmall U V q)
    (heq : ∀ t, p t = q t) :
    vkLoc F_U F_V hCompat hCover p hs =
      eqToHom (congrArg _ (p.source.symm.trans ((heq 0).trans q.source))) ≫
        vkLoc F_U F_V hCompat hCover q hs' ≫
          eqToHom (congrArg _
            (q.target.symm.trans ((heq 1).symm.trans p.target))) := by
  have ha : a = a' := p.source.symm.trans ((heq 0).trans q.source)
  have hb : b' = b := q.target.symm.trans ((heq 1).symm.trans p.target)
  subst ha
  subst hb
  have hpq : p = q := Path.ext (funext heq)
  subst hpq
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- A composite of two `eqToHom`s facing opposite ways is the identity. -/
private theorem vkEqToHom_mid {C : Type*} [Category C] {X Y : C} (p q : X = Y) :
    eqToHom p.symm ≫ eqToHom q = 𝟙 _ := by
  cases p
  cases q
  simp

/-- A composite of two `eqToHom`s facing the same way up to symmetry is the identity. -/
private theorem vkEqToHom_fwd {C : Type*} [Category C] {X Y : C} (p q : X = Y) :
    eqToHom p ≫ eqToHom q.symm = 𝟙 _ := by
  cases p
  cases q
  simp

/-- Reassociate a composite and cancel a middle `eqToHom` pair. -/
private theorem vkComp_mid {C : Type*} [Category C] {A B M N B' D : C}
    (e0 : A ⟶ B) (f : B ⟶ M) (m1 : M ⟶ N) (m2 : N ⟶ M) (g : M ⟶ B') (e1 : B' ⟶ D)
    (h : m1 ≫ m2 = 𝟙 M) :
    (e0 ≫ f ≫ m1) ≫ (m2 ≫ g ≫ e1) = e0 ≫ (f ≫ g) ≫ e1 := by
  calc (e0 ≫ f ≫ m1) ≫ (m2 ≫ g ≫ e1)
      = e0 ≫ f ≫ ((m1 ≫ m2) ≫ (g ≫ e1)) := by simp only [Category.assoc]
    _ = e0 ≫ f ≫ (g ≫ e1) := by rw [h, Category.id_comp]
    _ = e0 ≫ (f ≫ g) ≫ e1 := by simp only [Category.assoc]

/-- Square lemma in the `U` chart: corner paths have equal `loc` composites. -/
private theorem vkLoc_square_U {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {y00 y10 y01 y11 : X}
    (g : C(↥unitInterval × ↥unitInterval, X)) (hg : ∀ x, g x ∈ U)
    (bot : Path y00 y10) (rgt : Path y10 y11)
    (lft : Path y00 y01) (top : Path y01 y11)
    (hsBot : vkSmall U V bot) (hsRgt : vkSmall U V rgt)
    (hsLft : vkSmall U V lft) (hsTop : vkSmall U V top)
    (hbot : ∀ u : ↥unitInterval, bot u = g (u, 0))
    (hrgt : ∀ v : ↥unitInterval, rgt v = g (1, v))
    (hlft : ∀ v : ↥unitInterval, lft v = g (0, v))
    (htop : ∀ u : ↥unitInterval, top u = g (u, 1)) :
    vkLoc F_U F_V hCompat hCover bot hsBot ≫
      vkLoc F_U F_V hCompat hCover rgt hsRgt =
      vkLoc F_U F_V hCompat hCover lft hsLft ≫
        vkLoc F_U F_V hCompat hCover top hsTop := by
  have hBotU : Set.range ⇑bot ⊆ U := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [hbot u]
    exact hg _
  have hRgtU : Set.range ⇑rgt ⊆ U := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [hrgt u]
    exact hg _
  have hLftU : Set.range ⇑lft ⊆ U := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [hlft u]
    exact hg _
  have hTopU : Set.range ⇑top ⊆ U := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [htop u]
    exact hg _
  have eBot : vkLoc F_U F_V hCompat hCover bot hsBot =
      vkLU F_U F_V hCover bot hBotU :=
    vkLoc_of_mem_U F_U F_V hCompat hCover bot hsBot hBotU
  have eRgt : vkLoc F_U F_V hCompat hCover rgt hsRgt =
      vkLU F_U F_V hCover rgt hRgtU :=
    vkLoc_of_mem_U F_U F_V hCompat hCover rgt hsRgt hRgtU
  have eLft : vkLoc F_U F_V hCompat hCover lft hsLft =
      vkLU F_U F_V hCover lft hLftU :=
    vkLoc_of_mem_U F_U F_V hCompat hCover lft hsLft hLftU
  have eTop : vkLoc F_U F_V hCompat hCover top hsTop =
      vkLU F_U F_V hCover top hTopU :=
    vkLoc_of_mem_U F_U F_V hCompat hCover top hsTop hTopU
  rw [eBot, eRgt, eLft, eTop]
  set gU : C(↥unitInterval × ↥unitInterval, ↥U) :=
    ⟨fun x => ⟨g x, hg x⟩, Continuous.subtype_mk g.continuous hg⟩
  have hbotU : ∀ u : ↥unitInterval, vkRes U bot hBotU u = gU (u, 0) :=
    fun u => Subtype.ext (hbot u)
  have hrgtU : ∀ v : ↥unitInterval, vkRes U rgt hRgtU v = gU (1, v) :=
    fun v => Subtype.ext (hrgt v)
  have hlftU : ∀ v : ↥unitInterval, vkRes U lft hLftU v = gU (0, v) :=
    fun v => Subtype.ext (hlft v)
  have htopU : ∀ u : ↥unitInterval, vkRes U top hTopU u = gU (u, 1) :=
    fun u => Subtype.ext (htop u)
  have hcorner := vk_corner_square gU (vkRes U bot hBotU) (vkRes U rgt hRgtU)
    (vkRes U lft hLftU) (vkRes U top hTopU) hbotU hrgtU hlftU htopU
  have hF0 := congrArg F_U.map hcorner
  simp only [← FundamentalGroupoid.comp_eq] at hF0
  rw [Functor.map_comp, Functor.map_comp] at hF0
  have hF : F_U.map (Path.Homotopic.Quotient.mk (vkRes U bot hBotU)) ≫
        F_U.map (Path.Homotopic.Quotient.mk (vkRes U rgt hRgtU)) =
      F_U.map (Path.Homotopic.Quotient.mk (vkRes U lft hLftU)) ≫
        F_U.map (Path.Homotopic.Quotient.mk (vkRes U top hTopU)) := hF0
  have hmid10 := vkEqToHom_mid
    (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset hBotU ⟨1, bot.target⟩))
    (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset hRgtU ⟨0, rgt.source⟩))
  have hmid01 := vkEqToHom_mid
    (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset hLftU ⟨1, lft.target⟩))
    (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset hTopU ⟨0, top.source⟩))
  have hout00 := vkEqToHom_eq
    (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset hBotU ⟨0, bot.source⟩))
    (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset hLftU ⟨0, lft.source⟩))
  have hout11 := vkEqToHom_eq
    (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset hRgtU ⟨1, rgt.target⟩)).symm
    (vkObj0_eq_U F_U F_V hCover (vkMem_of_subset hTopU ⟨1, top.target⟩)).symm
  have hLHS : vkLU F_U F_V hCover bot hBotU ≫ vkLU F_U F_V hCover rgt hRgtU =
      eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset hBotU ⟨0, bot.source⟩)) ≫
        (F_U.map (Path.Homotopic.Quotient.mk (vkRes U bot hBotU)) ≫
          F_U.map (Path.Homotopic.Quotient.mk (vkRes U rgt hRgtU))) ≫
        eqToHom (vkObj0_eq_U F_U F_V hCover
          (vkMem_of_subset hRgtU ⟨1, rgt.target⟩)).symm := by
    calc vkLU F_U F_V hCover bot hBotU ≫ vkLU F_U F_V hCover rgt hRgtU
        = (eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hBotU ⟨0, bot.source⟩)) ≫
            F_U.map (Path.Homotopic.Quotient.mk (vkRes U bot hBotU)) ≫
            eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hBotU ⟨1, bot.target⟩)).symm) ≫
          (eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hRgtU ⟨0, rgt.source⟩)) ≫
            F_U.map (Path.Homotopic.Quotient.mk (vkRes U rgt hRgtU)) ≫
            eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hRgtU ⟨1, rgt.target⟩)).symm) := rfl
      _ = _ := vkComp_mid _ _ _ _ _ _ hmid10
  have hRHS : vkLU F_U F_V hCover lft hLftU ≫ vkLU F_U F_V hCover top hTopU =
      eqToHom (vkObj0_eq_U F_U F_V hCover
        (vkMem_of_subset hLftU ⟨0, lft.source⟩)) ≫
        (F_U.map (Path.Homotopic.Quotient.mk (vkRes U lft hLftU)) ≫
          F_U.map (Path.Homotopic.Quotient.mk (vkRes U top hTopU))) ≫
        eqToHom (vkObj0_eq_U F_U F_V hCover
          (vkMem_of_subset hTopU ⟨1, top.target⟩)).symm := by
    calc vkLU F_U F_V hCover lft hLftU ≫ vkLU F_U F_V hCover top hTopU
        = (eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hLftU ⟨0, lft.source⟩)) ≫
            F_U.map (Path.Homotopic.Quotient.mk (vkRes U lft hLftU)) ≫
            eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hLftU ⟨1, lft.target⟩)).symm) ≫
          (eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hTopU ⟨0, top.source⟩)) ≫
            F_U.map (Path.Homotopic.Quotient.mk (vkRes U top hTopU)) ≫
            eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hTopU ⟨1, top.target⟩)).symm) := rfl
      _ = _ := vkComp_mid _ _ _ _ _ _ hmid01
  rw [hLHS, hRHS, hF, hout00, hout11]

/-- Square lemma in the `V` chart. -/
private theorem vkLoc_square_V {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {y00 y10 y01 y11 : X}
    (g : C(↥unitInterval × ↥unitInterval, X)) (hg : ∀ x, g x ∈ V)
    (bot : Path y00 y10) (rgt : Path y10 y11)
    (lft : Path y00 y01) (top : Path y01 y11)
    (hsBot : vkSmall U V bot) (hsRgt : vkSmall U V rgt)
    (hsLft : vkSmall U V lft) (hsTop : vkSmall U V top)
    (hbot : ∀ u : ↥unitInterval, bot u = g (u, 0))
    (hrgt : ∀ v : ↥unitInterval, rgt v = g (1, v))
    (hlft : ∀ v : ↥unitInterval, lft v = g (0, v))
    (htop : ∀ u : ↥unitInterval, top u = g (u, 1)) :
    vkLoc F_U F_V hCompat hCover bot hsBot ≫
      vkLoc F_U F_V hCompat hCover rgt hsRgt =
      vkLoc F_U F_V hCompat hCover lft hsLft ≫
        vkLoc F_U F_V hCompat hCover top hsTop := by
  have hBotV : Set.range ⇑bot ⊆ V := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [hbot u]
    exact hg _
  have hRgtV : Set.range ⇑rgt ⊆ V := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [hrgt u]
    exact hg _
  have hLftV : Set.range ⇑lft ⊆ V := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [hlft u]
    exact hg _
  have hTopV : Set.range ⇑top ⊆ V := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [htop u]
    exact hg _
  have eBot : vkLoc F_U F_V hCompat hCover bot hsBot =
      vkLV F_U F_V hCompat hCover bot hBotV :=
    vkLoc_eq_lV F_U F_V hCompat hCover hsBot hBotV
  have eRgt : vkLoc F_U F_V hCompat hCover rgt hsRgt =
      vkLV F_U F_V hCompat hCover rgt hRgtV :=
    vkLoc_eq_lV F_U F_V hCompat hCover hsRgt hRgtV
  have eLft : vkLoc F_U F_V hCompat hCover lft hsLft =
      vkLV F_U F_V hCompat hCover lft hLftV :=
    vkLoc_eq_lV F_U F_V hCompat hCover hsLft hLftV
  have eTop : vkLoc F_U F_V hCompat hCover top hsTop =
      vkLV F_U F_V hCompat hCover top hTopV :=
    vkLoc_eq_lV F_U F_V hCompat hCover hsTop hTopV
  rw [eBot, eRgt, eLft, eTop]
  set gV : C(↥unitInterval × ↥unitInterval, ↥V) :=
    ⟨fun x => ⟨g x, hg x⟩, Continuous.subtype_mk g.continuous hg⟩
  have hbotV : ∀ u : ↥unitInterval, vkRes V bot hBotV u = gV (u, 0) :=
    fun u => Subtype.ext (hbot u)
  have hrgtV : ∀ v : ↥unitInterval, vkRes V rgt hRgtV v = gV (1, v) :=
    fun v => Subtype.ext (hrgt v)
  have hlftV : ∀ v : ↥unitInterval, vkRes V lft hLftV v = gV (0, v) :=
    fun v => Subtype.ext (hlft v)
  have htopV : ∀ u : ↥unitInterval, vkRes V top hTopV u = gV (u, 1) :=
    fun u => Subtype.ext (htop u)
  have hcorner := vk_corner_square gV (vkRes V bot hBotV) (vkRes V rgt hRgtV)
    (vkRes V lft hLftV) (vkRes V top hTopV) hbotV hrgtV hlftV htopV
  have hF0 := congrArg F_V.map hcorner
  simp only [← FundamentalGroupoid.comp_eq] at hF0
  rw [Functor.map_comp, Functor.map_comp] at hF0
  have hF : F_V.map (Path.Homotopic.Quotient.mk (vkRes V bot hBotV)) ≫
        F_V.map (Path.Homotopic.Quotient.mk (vkRes V rgt hRgtV)) =
      F_V.map (Path.Homotopic.Quotient.mk (vkRes V lft hLftV)) ≫
        F_V.map (Path.Homotopic.Quotient.mk (vkRes V top hTopV)) := hF0
  have hmid10 := vkEqToHom_mid
    (vkObj0_eq_V F_U F_V hCompat hCover (vkMem_of_subset hBotV ⟨1, bot.target⟩))
    (vkObj0_eq_V F_U F_V hCompat hCover (vkMem_of_subset hRgtV ⟨0, rgt.source⟩))
  have hmid01 := vkEqToHom_mid
    (vkObj0_eq_V F_U F_V hCompat hCover (vkMem_of_subset hLftV ⟨1, lft.target⟩))
    (vkObj0_eq_V F_U F_V hCompat hCover (vkMem_of_subset hTopV ⟨0, top.source⟩))
  have hout00 := vkEqToHom_eq
    (vkObj0_eq_V F_U F_V hCompat hCover (vkMem_of_subset hBotV ⟨0, bot.source⟩))
    (vkObj0_eq_V F_U F_V hCompat hCover (vkMem_of_subset hLftV ⟨0, lft.source⟩))
  have hout11 := vkEqToHom_eq
    (vkObj0_eq_V F_U F_V hCompat hCover
      (vkMem_of_subset hRgtV ⟨1, rgt.target⟩)).symm
    (vkObj0_eq_V F_U F_V hCompat hCover
      (vkMem_of_subset hTopV ⟨1, top.target⟩)).symm
  have hLHS : vkLV F_U F_V hCompat hCover bot hBotV ≫
      vkLV F_U F_V hCompat hCover rgt hRgtV =
      eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
        (vkMem_of_subset hBotV ⟨0, bot.source⟩)) ≫
        (F_V.map (Path.Homotopic.Quotient.mk (vkRes V bot hBotV)) ≫
          F_V.map (Path.Homotopic.Quotient.mk (vkRes V rgt hRgtV))) ≫
        eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
          (vkMem_of_subset hRgtV ⟨1, rgt.target⟩)).symm := by
    calc vkLV F_U F_V hCompat hCover bot hBotV ≫
            vkLV F_U F_V hCompat hCover rgt hRgtV
        = (eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hBotV ⟨0, bot.source⟩)) ≫
            F_V.map (Path.Homotopic.Quotient.mk (vkRes V bot hBotV)) ≫
            eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hBotV ⟨1, bot.target⟩)).symm) ≫
          (eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hRgtV ⟨0, rgt.source⟩)) ≫
            F_V.map (Path.Homotopic.Quotient.mk (vkRes V rgt hRgtV)) ≫
            eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hRgtV ⟨1, rgt.target⟩)).symm) := rfl
      _ = _ := vkComp_mid _ _ _ _ _ _ hmid10
  have hRHS : vkLV F_U F_V hCompat hCover lft hLftV ≫
      vkLV F_U F_V hCompat hCover top hTopV =
      eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
        (vkMem_of_subset hLftV ⟨0, lft.source⟩)) ≫
        (F_V.map (Path.Homotopic.Quotient.mk (vkRes V lft hLftV)) ≫
          F_V.map (Path.Homotopic.Quotient.mk (vkRes V top hTopV))) ≫
        eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
          (vkMem_of_subset hTopV ⟨1, top.target⟩)).symm := by
    calc vkLV F_U F_V hCompat hCover lft hLftV ≫
            vkLV F_U F_V hCompat hCover top hTopV
        = (eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hLftV ⟨0, lft.source⟩)) ≫
            F_V.map (Path.Homotopic.Quotient.mk (vkRes V lft hLftV)) ≫
            eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hLftV ⟨1, lft.target⟩)).symm) ≫
          (eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hTopV ⟨0, top.source⟩)) ≫
            F_V.map (Path.Homotopic.Quotient.mk (vkRes V top hTopV)) ≫
            eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hTopV ⟨1, top.target⟩)).symm) := rfl
      _ = _ := vkComp_mid _ _ _ _ _ _ hmid01
  rw [hLHS, hRHS, hF, hout00, hout11]

/-- Constant paths have trivial local value: `loc` is the `eqToHom` from `a = b`. -/
private theorem vkLoc_const {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} {p : Path a b} (hs : vkSmall U V p)
    (hconst : ∀ u, p u = a) :
    vkLoc F_U F_V hCompat hCover p hs =
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((hconst 1).symm.trans p.target)) := by
  have hab : a = b := (hconst 1).symm.trans p.target
  subst hab
  have hp : p = Path.refl a := Path.ext (funext hconst)
  subst hp
  simp only [eqToHom_refl]
  by_cases hU : Set.range (⇑(Path.refl a)) ⊆ U
  · have hLoc : vkLoc F_U F_V hCompat hCover (Path.refl a) hs =
        vkLU F_U F_V hCover (Path.refl a) hU :=
      vkLoc_of_mem_U F_U F_V hCompat hCover _ hs hU
    rw [hLoc]
    have hRes : vkRes U (Path.refl a) hU =
        Path.refl (⟨a, hU ⟨0, (Path.refl a).source⟩⟩ : ↥U) := by
      apply Path.ext
      rfl
    have hMk : F_U.map (Path.Homotopic.Quotient.mk (vkRes U (Path.refl a) hU)) =
        𝟙 _ := by
      calc F_U.map (Path.Homotopic.Quotient.mk (vkRes U (Path.refl a) hU))
          = F_U.map (Path.Homotopic.Quotient.mk
            (Path.refl (⟨a, hU ⟨0, (Path.refl a).source⟩⟩ : ↥U))) :=
            congrArg _ (congrArg _ hRes)
        _ = 𝟙 _ := CategoryTheory.Functor.map_id _ _
    have hLU : vkLU F_U F_V hCover (Path.refl a) hU = 𝟙 _ := by
      calc vkLU F_U F_V hCover (Path.refl a) hU
          = eqToHom (vkObj0_eq_U F_U F_V hCover
            (vkMem_of_subset hU ⟨0, (Path.refl a).source⟩)) ≫ 𝟙 _ ≫
            eqToHom (vkObj0_eq_U F_U F_V hCover
              (vkMem_of_subset hU ⟨1, (Path.refl a).target⟩)).symm :=
            congrArg (_ ≫ · ≫ _) hMk
        _ = 𝟙 _ := by
            simp only [Category.id_comp]
            exact (CategoryTheory.eqToHom_trans _ _).trans
              (CategoryTheory.eqToHom_refl _ _)
    rw [hLU]
  · have hV : Set.range (⇑(Path.refl a)) ⊆ V :=
      hs.resolve_left hU
    have hLoc : vkLoc F_U F_V hCompat hCover (Path.refl a) hs =
        vkLV F_U F_V hCompat hCover (Path.refl a) hV := by
      exact vkLoc_of_mem_V F_U F_V hCompat hCover _ hs hV hU
    rw [hLoc]
    have hRes : vkRes V (Path.refl a) hV =
        Path.refl (⟨a, hV ⟨0, (Path.refl a).source⟩⟩ : ↥V) := by
      apply Path.ext
      rfl
    have hMk : F_V.map (Path.Homotopic.Quotient.mk (vkRes V (Path.refl a) hV)) =
        𝟙 _ := by
      calc F_V.map (Path.Homotopic.Quotient.mk (vkRes V (Path.refl a) hV))
          = F_V.map (Path.Homotopic.Quotient.mk
            (Path.refl (⟨a, hV ⟨0, (Path.refl a).source⟩⟩ : ↥V))) :=
            congrArg _ (congrArg _ hRes)
        _ = 𝟙 _ := CategoryTheory.Functor.map_id _ _
    have hLV : vkLV F_U F_V hCompat hCover (Path.refl a) hV = 𝟙 _ := by
      calc vkLV F_U F_V hCompat hCover (Path.refl a) hV
          = eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
            (vkMem_of_subset hV ⟨0, (Path.refl a).source⟩)) ≫ 𝟙 _ ≫
            eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
              (vkMem_of_subset hV ⟨1, (Path.refl a).target⟩)).symm :=
            congrArg (_ ≫ · ≫ _) hMk
        _ = 𝟙 _ := by
            simp only [Category.id_comp]
            exact (CategoryTheory.eqToHom_trans _ _).trans
              (CategoryTheory.eqToHom_refl _ _)
    rw [hLV]

/-- Refinement in the `U` chart: splitting a subpath in two. -/
private theorem vkLoc_refine_U {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) {s t u : ↥unitInterval}
    (hst : s ≤ t) (htu : t ≤ u)
    (hsST : vkSmall U V (γ.subpath s t))
    (hsTU : vkSmall U V (γ.subpath t u))
    (hsSU : vkSmall U V (γ.subpath s u))
    (hW : Set.range ⇑(γ.subpath s u) ⊆ U) :
    vkLoc F_U F_V hCompat hCover (γ.subpath s t) hsST ≫
      vkLoc F_U F_V hCompat hCover (γ.subpath t u) hsTU =
      vkLoc F_U F_V hCompat hCover (γ.subpath s u) hsSU := by
  have hsu : s ≤ u := le_trans hst htu
  have hsub : ∀ (p q : ↥unitInterval) (w : ↥unitInterval),
      (γ.subpath p q) w = γ (Set.Icc.convexComb p q w : ↥unitInterval) :=
    fun p q w => rfl
  have hinner : Continuous (fun p : ↥unitInterval × ↥unitInterval =>
      (Set.Icc.convexComb (Set.Icc.convexComb s t p.1) u p.2 :
        ↥unitInterval)) := by
    fun_prop
  set g : C(↥unitInterval × ↥unitInterval, X) :=
    ⟨fun p => γ (Set.Icc.convexComb (Set.Icc.convexComb s t p.1) u p.2 :
      ↥unitInterval), γ.continuous.comp hinner⟩ with hgdef
  have hg_eq : ∀ u_ v : ↥unitInterval,
      g (u_, v) = γ (Set.Icc.convexComb (Set.Icc.convexComb s t u_) u v :
        ↥unitInterval) :=
    fun u_ v => rfl
  have hgU : ∀ x : ↥unitInterval × ↥unitInterval, g x ∈ U := by
    intro x
    have hsc : s ≤ (Set.Icc.convexComb s t x.1 : ↥unitInterval) :=
      Set.Icc.le_convexComb hst x.1
    have hct : (Set.Icc.convexComb s t x.1 : ↥unitInterval) ≤ t :=
      Set.Icc.convexComb_le hst x.1
    have hcu : (Set.Icc.convexComb s t x.1 : ↥unitInterval) ≤ u :=
      le_trans hct htu
    have hcw : (Set.Icc.convexComb s t x.1 : ↥unitInterval) ≤
        (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
          ↥unitInterval) :=
      Set.Icc.le_convexComb hcu x.2
    have hwu : (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) ≤ u :=
      Set.Icc.convexComb_le hcu x.2
    have hsw : s ≤ (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) :=
      le_trans hsc hcw
    have hmem : (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) ∈ Set.Icc s u :=
      Set.mem_Icc.mpr ⟨hsw, hwu⟩
    have hrange : γ (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) ∈ Set.range ⇑(γ.subpath s u) := by
      rw [Path.range_subpath_of_le _ _ _ hsu]
      exact ⟨_, hmem, rfl⟩
    have hgx : g x = γ (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) :=
      hg_eq x.1 x.2
    rw [hgx]
    exact hW hrange
  have hbot : ∀ w : ↥unitInterval, (γ.subpath s t) w = g (w, 0) := by
    intro w
    rw [hsub s t w, hg_eq w 0, Set.Icc.convexComb_zero]
  have hrgt : ∀ v : ↥unitInterval, (γ.subpath t u) v = g (1, v) := by
    intro v
    rw [hsub t u v, hg_eq 1 v, Set.Icc.convexComb_one]
  have hlft : ∀ v : ↥unitInterval, (γ.subpath s u) v = g (0, v) := by
    intro v
    rw [hsub s u v, hg_eq 0 v, Set.Icc.convexComb_zero]
  have hrefl : ∀ w : ↥unitInterval, (Path.refl (γ u)) w = γ u :=
    fun w => rfl
  have htop : ∀ w : ↥unitInterval, (Path.refl (γ u)) w = g (w, 1) := by
    intro w
    rw [hrefl w, hg_eq w 1, Set.Icc.convexComb_one]
  have hmem_u : γ u ∈ U := by
    have h1 : (γ.subpath s u) 1 = γ u := by
      rw [hsub s u 1, Set.Icc.convexComb_one]
    exact hW ⟨1, h1⟩
  have hsTop : vkSmall U V (Path.refl (γ u)) := by
    left
    intro x hx
    obtain ⟨w, hw⟩ := hx
    rw [← hw, hrefl w]
    exact hmem_u
  have hsq := vkLoc_square_U F_U F_V hCompat hCover g hgU
    (γ.subpath s t) (γ.subpath t u) (γ.subpath s u) (Path.refl (γ u))
    hsST hsTU hsSU hsTop hbot hrgt hlft htop
  have hrefl1 : vkLoc F_U F_V hCompat hCover (Path.refl (γ u)) hsTop = 𝟙 _ := by
    have hc := vkLoc_const F_U F_V hCompat hCover hsTop (fun w => hrefl w)
    rw [hc]
    exact CategoryTheory.eqToHom_refl _ _
  rw [hrefl1, Category.comp_id] at hsq
  exact hsq

/-- Refinement in the `V` chart: splitting a subpath in two. -/
private theorem vkLoc_refine_V {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) {s t u : ↥unitInterval}
    (hst : s ≤ t) (htu : t ≤ u)
    (hsST : vkSmall U V (γ.subpath s t))
    (hsTU : vkSmall U V (γ.subpath t u))
    (hsSU : vkSmall U V (γ.subpath s u))
    (hW : Set.range ⇑(γ.subpath s u) ⊆ V) :
    vkLoc F_U F_V hCompat hCover (γ.subpath s t) hsST ≫
      vkLoc F_U F_V hCompat hCover (γ.subpath t u) hsTU =
      vkLoc F_U F_V hCompat hCover (γ.subpath s u) hsSU := by
  have hsu : s ≤ u := le_trans hst htu
  have hsub : ∀ (p q : ↥unitInterval) (w : ↥unitInterval),
      (γ.subpath p q) w = γ (Set.Icc.convexComb p q w : ↥unitInterval) :=
    fun p q w => rfl
  have hinner : Continuous (fun p : ↥unitInterval × ↥unitInterval =>
      (Set.Icc.convexComb (Set.Icc.convexComb s t p.1) u p.2 :
        ↥unitInterval)) := by
    fun_prop
  set g : C(↥unitInterval × ↥unitInterval, X) :=
    ⟨fun p => γ (Set.Icc.convexComb (Set.Icc.convexComb s t p.1) u p.2 :
      ↥unitInterval), γ.continuous.comp hinner⟩ with hgdef
  have hg_eq : ∀ u_ v : ↥unitInterval,
      g (u_, v) = γ (Set.Icc.convexComb (Set.Icc.convexComb s t u_) u v :
        ↥unitInterval) :=
    fun u_ v => rfl
  have hgV : ∀ x : ↥unitInterval × ↥unitInterval, g x ∈ V := by
    intro x
    have hsc : s ≤ (Set.Icc.convexComb s t x.1 : ↥unitInterval) :=
      Set.Icc.le_convexComb hst x.1
    have hct : (Set.Icc.convexComb s t x.1 : ↥unitInterval) ≤ t :=
      Set.Icc.convexComb_le hst x.1
    have hcu : (Set.Icc.convexComb s t x.1 : ↥unitInterval) ≤ u :=
      le_trans hct htu
    have hcw : (Set.Icc.convexComb s t x.1 : ↥unitInterval) ≤
        (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
          ↥unitInterval) :=
      Set.Icc.le_convexComb hcu x.2
    have hwu : (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) ≤ u :=
      Set.Icc.convexComb_le hcu x.2
    have hsw : s ≤ (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) :=
      le_trans hsc hcw
    have hmem : (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) ∈ Set.Icc s u :=
      Set.mem_Icc.mpr ⟨hsw, hwu⟩
    have hrange : γ (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) ∈ Set.range ⇑(γ.subpath s u) := by
      rw [Path.range_subpath_of_le _ _ _ hsu]
      exact ⟨_, hmem, rfl⟩
    have hgx : g x = γ (Set.Icc.convexComb (Set.Icc.convexComb s t x.1) u x.2 :
        ↥unitInterval) :=
      hg_eq x.1 x.2
    rw [hgx]
    exact hW hrange
  have hbot : ∀ w : ↥unitInterval, (γ.subpath s t) w = g (w, 0) := by
    intro w
    rw [hsub s t w, hg_eq w 0, Set.Icc.convexComb_zero]
  have hrgt : ∀ v : ↥unitInterval, (γ.subpath t u) v = g (1, v) := by
    intro v
    rw [hsub t u v, hg_eq 1 v, Set.Icc.convexComb_one]
  have hlft : ∀ v : ↥unitInterval, (γ.subpath s u) v = g (0, v) := by
    intro v
    rw [hsub s u v, hg_eq 0 v, Set.Icc.convexComb_zero]
  have hrefl : ∀ w : ↥unitInterval, (Path.refl (γ u)) w = γ u :=
    fun w => rfl
  have htop : ∀ w : ↥unitInterval, (Path.refl (γ u)) w = g (w, 1) := by
    intro w
    rw [hrefl w, hg_eq w 1, Set.Icc.convexComb_one]
  have hmem_u : γ u ∈ V := by
    have h1 : (γ.subpath s u) 1 = γ u := by
      rw [hsub s u 1, Set.Icc.convexComb_one]
    exact hW ⟨1, h1⟩
  have hsTop : vkSmall U V (Path.refl (γ u)) := by
    right
    intro x hx
    obtain ⟨w, hw⟩ := hx
    rw [← hw, hrefl w]
    exact hmem_u
  have hsq := vkLoc_square_V F_U F_V hCompat hCover g hgV
    (γ.subpath s t) (γ.subpath t u) (γ.subpath s u) (Path.refl (γ u))
    hsST hsTU hsSU hsTop hbot hrgt hlft htop
  have hrefl1 : vkLoc F_U F_V hCompat hCover (Path.refl (γ u)) hsTop = 𝟙 _ := by
    have hc := vkLoc_const F_U F_V hCompat hCover hsTop (fun w => hrefl w)
    rw [hc]
    exact CategoryTheory.eqToHom_refl _ _
  rw [hrefl1, Category.comp_id] at hsq
  exact hsq

/-- A point of a grid cell is within `1 / N` of the cell corner. -/
private theorem vkGrid_dist_le {N k : ℕ} (t : ↥unitInterval)
    (hlo : vkGrid N k ≤ t) (hhi : t ≤ vkGrid N (k + 1)) :
    dist t (vkGrid N k) ≤ 1 / ((N : ℕ) : ℝ) := by
  exact unitInterval.dist_uniformGrid_left_le t hlo hhi

/-- Lebesgue grids in 1D: every path admits some uniform grid. -/
private theorem vkLebesgue1D {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) : ∃ N, 1 ≤ N ∧ vkAdm U V γ N := by
  let W : Bool → TopologicalSpace.Opens X
    | false => ⟨U, hU⟩
    | true => ⟨V, hV⟩
  have hW : TopologicalSpace.IsOpenCover W := by
    apply TopologicalSpace.IsOpenCover.of_sets
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx : x ∈ U ∪ V := by
      rw [hCover]
      exact Set.mem_univ x
    rcases hx with hxU | hxV
    · exact ⟨false, hxU⟩
    · exact ⟨true, hxV⟩
  obtain ⟨N, hN, hsub⟩ := exists_uniformGrid_subordinate W hW γ
  refine ⟨N, hN, ?_⟩
  intro k
  obtain ⟨i, hi⟩ := hsub k
  cases i with
  | false => exact Or.inl hi
  | true => exact Or.inr hi

/-- Lebesgue grids in 2D: every square admits a uniform grid of small cells. -/
private theorem vkLebesgue2D {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    (H : C(↥unitInterval × ↥unitInterval, X)) :
    ∃ N, 1 ≤ N ∧ ∀ i j,
      (∀ x ∈ Set.Icc (vkGrid N i) (vkGrid N (i + 1)) ×ˢ
        Set.Icc (vkGrid N j) (vkGrid N (j + 1)), H x ∈ U) ∨
      (∀ x ∈ Set.Icc (vkGrid N i) (vkGrid N (i + 1)) ×ˢ
        Set.Icc (vkGrid N j) (vkGrid N (j + 1)), H x ∈ V) := by
  set c : Bool → Set (↥unitInterval × ↥unitInterval) := fun i => match i with
    | false => H ⁻¹' U
    | true => H ⁻¹' V
  have hc1 : ∀ i, IsOpen (c i) := by
    intro i
    cases i
    · exact H.continuous.isOpen_preimage _ hU
    · exact H.continuous.isOpen_preimage _ hV
  have hc2 : Set.univ ⊆ ⋃ i, c i := by
    intro t _
    have hmem : H t ∈ U ∪ V := by
      rw [hCover]
      exact Set.mem_univ _
    rcases hmem with h | h
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc1 hc2
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  have hN : (1 : ℝ) / (((n + 1 : ℕ)) : ℝ) < δ := by
    have hcast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    exact hn
  refine ⟨n + 1, by omega, ?_⟩
  intro i j
  have hcell : ∀ x : ↥unitInterval × ↥unitInterval,
      x ∈ Set.Icc (vkGrid (n + 1) i) (vkGrid (n + 1) (i + 1)) ×ˢ
          Set.Icc (vkGrid (n + 1) j) (vkGrid (n + 1) (j + 1)) →
      dist x (vkGrid (n + 1) i, vkGrid (n + 1) j) < δ := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    obtain ⟨hlo1, hhi1⟩ := Set.mem_Icc.mp hx1
    obtain ⟨hlo2, hhi2⟩ := Set.mem_Icc.mp hx2
    have d1 : dist x.1 (vkGrid (n + 1) i) < δ :=
      lt_of_le_of_lt (vkGrid_dist_le x.1 hlo1 hhi1) hN
    have d2 : dist x.2 (vkGrid (n + 1) j) < δ :=
      lt_of_le_of_lt (vkGrid_dist_le x.2 hlo2 hhi2) hN
    rw [Prod.dist_eq]
    exact max_lt_iff.mpr ⟨d1, d2⟩
  obtain ⟨b, hb⟩ := hδ (vkGrid (n + 1) i, vkGrid (n + 1) j) (Set.mem_univ _)
  cases b with
  | false =>
    left
    intro x hx
    have hxb := hcell x hx
    have hcb : x ∈ c false := hb (Metric.mem_ball.mpr hxb)
    exact hcb
  | true =>
    right
    intro x hx
    have hxb := hcell x hx
    have hcb : x ∈ c true := hb (Metric.mem_ball.mpr hxb)
    exact hcb

/-- Chained local values along a sequence of small paths. -/
private noncomputable def vkChainSeq {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    (z : ℕ → X) (P : ∀ k, Path (z k) (z (k + 1)))
    (hs : ∀ k, vkSmall U V (P k)) : ∀ m, vkObj0 F_U F_V hCover (z 0) ⟶
      vkObj0 F_U F_V hCover (z m)
  | 0 => 𝟙 _
  | m + 1 => vkChainSeq F_U F_V hCompat hCover z P hs m ≫
      vkLoc F_U F_V hCompat hCover (P m) (hs m)

/-- Appending chains corresponds to composition. -/
private theorem vkChainSeq_append {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    (z : ℕ → X) (P : ∀ k, Path (z k) (z (k + 1)))
    (hs : ∀ k, vkSmall U V (P k)) (m1 m2 : ℕ) :
    vkChainSeq F_U F_V hCompat hCover z P hs (m1 + m2) =
      vkChainSeq F_U F_V hCompat hCover z P hs m1 ≫
        vkChainSeq F_U F_V hCompat hCover (fun k => z (m1 + k))
          (fun k => P (m1 + k)) (fun k => hs (m1 + k)) m2 := by
  induction m2 generalizing m1 with
  | zero => simp [vkChainSeq, Nat.add_zero, Category.comp_id]
  | succ m2 ih =>
    calc vkChainSeq F_U F_V hCompat hCover z P hs (m1 + (m2 + 1))
        = vkChainSeq F_U F_V hCompat hCover z P hs ((m1 + m2) + 1) := rfl
      _ = vkChainSeq F_U F_V hCompat hCover z P hs (m1 + m2) ≫
          vkLoc F_U F_V hCompat hCover (P (m1 + m2)) (hs (m1 + m2)) := rfl
      _ = (vkChainSeq F_U F_V hCompat hCover z P hs m1 ≫
          vkChainSeq F_U F_V hCompat hCover (fun k => z (m1 + k))
            (fun k => P (m1 + k)) (fun k => hs (m1 + k)) m2) ≫
          vkLoc F_U F_V hCompat hCover (P (m1 + m2)) (hs (m1 + m2)) :=
          congrArg (· ≫ _) (ih m1)
      _ = vkChainSeq F_U F_V hCompat hCover z P hs m1 ≫
          (vkChainSeq F_U F_V hCompat hCover (fun k => z (m1 + k))
            (fun k => P (m1 + k)) (fun k => hs (m1 + k)) m2 ≫
          vkLoc F_U F_V hCompat hCover (P (m1 + m2)) (hs (m1 + m2))) := by
          rw [Category.assoc]
      _ = vkChainSeq F_U F_V hCompat hCover z P hs m1 ≫
          vkChainSeq F_U F_V hCompat hCover (fun k => z (m1 + k))
            (fun k => P (m1 + k)) (fun k => hs (m1 + k)) (m2 + 1) := rfl

/-- Unfolding a chain at a successor index. -/
private theorem vkChainSeq_succ {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    (z : ℕ → X) (P : ∀ k, Path (z k) (z (k + 1)))
    (hs : ∀ k, vkSmall U V (P k)) (m : ℕ) :
    vkChainSeq F_U F_V hCompat hCover z P hs (m + 1) =
      vkChainSeq F_U F_V hCompat hCover z P hs m ≫
        vkLoc F_U F_V hCompat hCover (P m) (hs m) := rfl

/-- Unfolding a chain at zero. -/
private theorem vkChainSeq_zero {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    (z : ℕ → X) (P : ∀ k, Path (z k) (z (k + 1)))
    (hs : ∀ k, vkSmall U V (P k)) :
    vkChainSeq F_U F_V hCompat hCover z P hs 0 = 𝟙 _ := rfl

/-- Congruence of chains under pointwise-equal data. -/
private theorem vkChainSeq_congr {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    (z z' : ℕ → X) (P : ∀ k, Path (z k) (z (k + 1)))
    (P' : ∀ k, Path (z' k) (z' (k + 1)))
    (hs : ∀ k, vkSmall U V (P k)) (hs' : ∀ k, vkSmall U V (P' k))
    (m : ℕ) (hz : ∀ k, k ≤ m → z k = z' k)
    (hm : ∀ k, k < m → ∀ s : ↥unitInterval, P k s = P' k s) :
      vkChainSeq F_U F_V hCompat hCover z P hs m =
        eqToHom (congrArg (vkObj0 F_U F_V hCover) (hz 0 (Nat.zero_le m))) ≫
          vkChainSeq F_U F_V hCompat hCover z' P' hs' m ≫
          eqToHom (congrArg (vkObj0 F_U F_V hCover) (hz m le_rfl)).symm := by
  revert hz hm
  induction m with
  | zero =>
    intro hz hm
    rw [vkChainSeq_zero, vkChainSeq_zero, Category.id_comp,
      CategoryTheory.eqToHom_trans]
    exact (CategoryTheory.eqToHom_refl _ _).symm
  | succ m ih =>
    intro hz hm
    have hz' : ∀ k, k ≤ m → z k = z' k := fun k hk => hz k (by omega)
    have hm' : ∀ k, k < m → ∀ s, P k s = P' k s :=
      fun k hk s => hm k (by omega) s
    have hmM : ∀ s : ↥unitInterval, P m s = P' m s := hm m (by omega)
    have ihm := ih hz' hm'
    have hloc := vkLoc_congr F_U F_V hCompat hCover (hs m) (hs' m) hmM
    have hmid := vkEqToHom_mid
      (congrArg (vkObj0 F_U F_V hCover) (hz' m le_rfl))
      (congrArg (vkObj0 F_U F_V hCover)
        ((P m).source.symm.trans ((hmM 0).trans (P' m).source)))
    have he0 : eqToHom (congrArg (vkObj0 F_U F_V hCover) (hz' 0 (Nat.zero_le m))) =
        eqToHom (congrArg (vkObj0 F_U F_V hCover) (hz 0 (Nat.zero_le (m + 1)))) :=
      vkEqToHom_eq _ _
    have he1 : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((P' m).target.symm.trans ((hmM 1).symm.trans (P m).target))) =
        eqToHom (congrArg (vkObj0 F_U F_V hCover) (hz (m + 1) le_rfl)).symm :=
      vkEqToHom_eq _ _
    rw [vkChainSeq_succ, vkChainSeq_succ, ihm, hloc,
      vkComp_mid _ _ _ _ _ _ hmid, he0, he1]

/-- Grid chain of a path at an admissible grid. -/
private noncomputable def vkChain {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) (N : ℕ) (hN : 1 ≤ N) (hA : vkAdm U V γ N) :
    vkObj0 F_U F_V hCover a ⟶ vkObj0 F_U F_V hCover b :=
  eqToHom (congrArg _ ((congrArg γ (vkGrid_zero N)).trans γ.source)).symm ≫
    vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
      (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1))) (fun k => hA k) N ≫
      eqToHom (congrArg _ ((congrArg γ (vkGrid_top hN le_rfl)).trans γ.target))

/-- A chain over a monotone time grid inside `U` equals `loc` of the long subpath. -/
private theorem vkTelescope_U {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) (τ : ℕ → ↥unitInterval)
    (hτ : Monotone τ)
    (hs : ∀ k, vkSmall U V (γ.subpath (τ k) (τ (k + 1))))
    (m : ℕ) (hW : ∀ j, j ≤ m → Set.range ⇑(γ.subpath (τ 0) (τ j)) ⊆ U) :
    vkChainSeq F_U F_V hCompat hCover (fun k => γ (τ k))
      (fun k => γ.subpath (τ k) (τ (k + 1))) hs m =
      vkLoc F_U F_V hCompat hCover (γ.subpath (τ 0) (τ m))
        (Or.inl (hW m le_rfl)) := by
  revert hW
  induction m with
  | zero =>
    intro hW
    rw [vkChainSeq_zero]
    have hsub0 : ∀ w : ↥unitInterval, (γ.subpath (τ 0) (τ 0)) w = γ (τ 0) := by
      intro w
      have e : (γ.subpath (τ 0) (τ 0)) w =
          γ (Set.Icc.convexComb (τ 0) (τ 0) w : ↥unitInterval) := rfl
      rw [e, Set.Icc.convexComb_eq]
    have hc := vkLoc_const F_U F_V hCompat hCover (Or.inl (hW 0 le_rfl)) hsub0
    rw [hc]
    exact (CategoryTheory.eqToHom_refl _ _).symm
  | succ m ih =>
    intro hW
    have hWm : ∀ j, j ≤ m → Set.range ⇑(γ.subpath (τ 0) (τ j)) ⊆ U :=
      fun j hj => hW j (by omega)
    have ihm := ih hWm
    have h01 : τ 0 ≤ τ m := hτ (Nat.zero_le m)
    have h12 : τ m ≤ τ (m + 1) := hτ (Nat.le_succ m)
    rw [vkChainSeq_succ, ihm]
    exact vkLoc_refine_U F_U F_V hCompat hCover γ h01 h12
      (Or.inl (hWm m le_rfl)) (hs m) (Or.inl (hW (m + 1) le_rfl))
      (hW (m + 1) le_rfl)

/-- A chain over a monotone time grid inside `V` equals `loc` of the long subpath. -/
private theorem vkTelescope_V {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) (τ : ℕ → ↥unitInterval)
    (hτ : Monotone τ)
    (hs : ∀ k, vkSmall U V (γ.subpath (τ k) (τ (k + 1))))
    (m : ℕ) (hW : ∀ j, j ≤ m → Set.range ⇑(γ.subpath (τ 0) (τ j)) ⊆ V) :
    vkChainSeq F_U F_V hCompat hCover (fun k => γ (τ k))
      (fun k => γ.subpath (τ k) (τ (k + 1))) hs m =
      vkLoc F_U F_V hCompat hCover (γ.subpath (τ 0) (τ m))
        (Or.inr (hW m le_rfl)) := by
  revert hW
  induction m with
  | zero =>
    intro hW
    rw [vkChainSeq_zero]
    have hsub0 : ∀ w : ↥unitInterval, (γ.subpath (τ 0) (τ 0)) w = γ (τ 0) := by
      intro w
      have e : (γ.subpath (τ 0) (τ 0)) w =
          γ (Set.Icc.convexComb (τ 0) (τ 0) w : ↥unitInterval) := rfl
      rw [e, Set.Icc.convexComb_eq]
    have hc := vkLoc_const F_U F_V hCompat hCover (Or.inr (hW 0 le_rfl)) hsub0
    rw [hc]
    exact (CategoryTheory.eqToHom_refl _ _).symm
  | succ m ih =>
    intro hW
    have hWm : ∀ j, j ≤ m → Set.range ⇑(γ.subpath (τ 0) (τ j)) ⊆ V :=
      fun j hj => hW j (by omega)
    have ihm := ih hWm
    have h01 : τ 0 ≤ τ m := hτ (Nat.zero_le m)
    have h12 : τ m ≤ τ (m + 1) := hτ (Nat.le_succ m)
    rw [vkChainSeq_succ, ihm]
    exact vkLoc_refine_V F_U F_V hCompat hCover γ h01 h12
      (Or.inr (hWm m le_rfl)) (hs m) (Or.inr (hW (m + 1) le_rfl))
      (hW (m + 1) le_rfl)
/-- Grid points at index `0` agree across refinements. -/
private theorem vkGrid_zero_eq {N M : ℕ} : vkGrid (M * N) 0 = vkGrid N 0 := by
  rw [vkGrid_zero, vkGrid_zero]

/-- Block structure, mirrored: the `(M * N)`-grid point `M * j` is the
`N`-grid point `j`. Rewriting grid indices is safe here since `vkGrid` lands
in the fixed type `↥unitInterval`. -/
private theorem vkGrid_block_eq' {N M j : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hj : j ≤ N) : vkGrid (M * N) (M * j) = vkGrid N j := by
  rw [Nat.mul_comm M N, Nat.mul_comm M j]
  exact vkGrid_block_eq hN hM hj

/-- Grid independence, auxiliary induction: the `(M * N)`-chain at `M * j`
agrees with the `N`-chain at `j`. The mirrored index order keeps every
successor step definitional (`M * (j + 1)` unfolds to `M * j + M`), so no
rewriting inside dependent chain indices is ever needed. -/
private theorem vkGrid_indep_aux {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hA : vkAdm U V γ N) (hANM : vkAdm U V γ (M * N))
    (j : ℕ) (hj : j ≤ N) :
    vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid (M * N) k))
      (fun k => γ.subpath (vkGrid (M * N) k) (vkGrid (M * N) (k + 1)))
      (fun k => hANM k) (M * j) =
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        (congrArg γ vkGrid_zero_eq)) ≫
        vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
          (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
          (fun k => hA k) j ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          (congrArg γ (vkGrid_block_eq' hN hM hj))).symm := by
  revert hj
  induction j with
  | zero =>
    intro hj
    change vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid (M * N) k))
      (fun k => γ.subpath (vkGrid (M * N) k) (vkGrid (M * N) (k + 1)))
      (fun k => hANM k) 0 = _
    rw [vkChainSeq_zero, vkChainSeq_zero, Category.id_comp,
      CategoryTheory.eqToHom_trans]
    exact (CategoryTheory.eqToHom_refl _ _).symm
  | succ j ih =>
    intro hj1
    have hj : j ≤ N := Nat.le_of_succ_le hj1
    have ihm := ih hj
    set τ : ℕ → ↥unitInterval := fun k => vkGrid (M * N) (M * j + k)
    have hτmono : Monotone τ := fun a b hab =>
      vkGrid_mono _ (Nat.add_le_add_left hab _)
    have hring1 : ∀ k, vkGrid (M * N) ((M * j + k) + 1) =
        vkGrid (M * N) (M * j + (k + 1)) :=
      fun k => congrArg _ (by omega)
    have hsτ : ∀ k, vkSmall U V (γ.subpath (τ k) (τ (k + 1))) := by
      intro k
      have h1 := hANM (M * j + k)
      change vkSmall U V
        (γ.subpath (vkGrid (M * N) (M * j + k)) (vkGrid (M * N) (M * j + (k + 1))))
      rw [← hring1 k]
      exact h1
    have hsub_cell : ∀ t, t ≤ M →
        Set.range ⇑(γ.subpath (τ 0) (τ t)) ⊆
          γ '' Set.Icc (vkGrid N j) (vkGrid N (j + 1)) := by
      intro t ht
      have hAB : τ 0 ≤ τ t := hτmono (Nat.zero_le t)
      have hA0 : τ 0 = vkGrid N j := vkGrid_block_eq' hN hM hj
      have hle : M * j + t ≤ M * (j + 1) := by
        have e : M * (j + 1) = M * j + M := by ring
        have h : M * j + t ≤ M * j + M := Nat.add_le_add_left ht _
        rwa [← e] at h
      have hBt : τ t ≤ vkGrid N (j + 1) := by
        have h1 : vkGrid (M * N) (M * j + t) ≤ vkGrid (M * N) (M * (j + 1)) :=
          vkGrid_mono _ hle
        rw [vkGrid_block_eq' hN hM hj1] at h1
        exact h1
      have hIcc : Set.Icc (τ 0) (τ t) ⊆ Set.Icc (vkGrid N j) (vkGrid N (j + 1)) := by
        rw [hA0]
        exact Set.Icc_subset_Icc le_rfl hBt
      change Set.range ⇑(γ.subpath (vkGrid (M * N) (M * j))
        (vkGrid (M * N) (M * j + t))) ⊆ _
      have hle0 : vkGrid (M * N) (M * j) ≤ vkGrid (M * N) (M * j + t) :=
        vkGrid_mono _ (by omega)
      rw [Path.range_subpath_of_le _ _ _ hle0]
      exact Set.image_mono hIcc
    have heqUN : ∀ s : ↥unitInterval, (γ.subpath (τ 0) (τ M)) s =
        (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) s := by
      intro s
      have e1 : (γ.subpath (τ 0) (τ M)) s =
          γ (Set.Icc.convexComb (τ 0) (τ M) s : ↥unitInterval) := rfl
      have e2 : (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) s =
          γ (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) s :
            ↥unitInterval) := rfl
      have h1 : τ 0 = vkGrid N j := vkGrid_block_eq' hN hM hj
      have h2 : τ M = vkGrid N (j + 1) := by
        have h : vkGrid (M * N) (M * j + M) = vkGrid N (j + 1) := by
          rw [show M * j + M = M * (j + 1) from by ring]
          exact vkGrid_block_eq' hN hM hj1
        exact h
      rw [e1, e2, h1, h2]
    have hzdata : ∀ k, k ≤ M →
        (fun k => (fun k' => γ (vkGrid (M * N) k')) (M * j + k)) k =
          (fun k => γ (τ k)) k :=
      fun k _ => rfl
    have hmdata : ∀ k, k < M → ∀ s : ↥unitInterval,
        (fun k => (fun k' => γ.subpath (vkGrid (M * N) k')
          (vkGrid (M * N) (k' + 1))) (M * j + k)) k s =
          (fun k => γ.subpath (τ k) (τ (k + 1))) k s := by
      intro k _ s
      have e1 : (fun k => (fun k' => γ.subpath (vkGrid (M * N) k')
          (vkGrid (M * N) (k' + 1))) (M * j + k)) k s =
          γ (Set.Icc.convexComb (vkGrid (M * N) (M * j + k))
            (vkGrid (M * N) ((M * j + k) + 1)) s : ↥unitInterval) := rfl
      have e2 : (fun k => γ.subpath (τ k) (τ (k + 1))) k s =
          γ (Set.Icc.convexComb (τ k) (τ (k + 1)) s : ↥unitInterval) := rfl
      rw [e1, e2, hring1 k]
    have hbridge : vkChainSeq F_U F_V hCompat hCover
        (fun k => (fun k' => γ (vkGrid (M * N) k')) (M * j + k))
        (fun k => (fun k' => γ.subpath (vkGrid (M * N) k')
          (vkGrid (M * N) (k' + 1))) (M * j + k))
        (fun k => (fun k => hANM k) (M * j + k)) M =
        eqToHom (congrArg (vkObj0 F_U F_V hCover) (hzdata 0 (Nat.zero_le M))) ≫
          vkChainSeq F_U F_V hCompat hCover (fun k => γ (τ k))
            (fun k => γ.subpath (τ k) (τ (k + 1))) hsτ M ≫
          eqToHom (congrArg (vkObj0 F_U F_V hCover)
            (hzdata M le_rfl)).symm :=
      vkChainSeq_congr F_U F_V hCompat hCover _ _ _ _ _ _ _ hzdata hmdata
    have happ := vkChainSeq_append F_U F_V hCompat hCover
      (fun k => γ (vkGrid (M * N) k))
      (fun k => γ.subpath (vkGrid (M * N) k) (vkGrid (M * N) (k + 1)))
      (fun k => hANM k) (M * j) M
    have hmid : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          (congrArg γ (vkGrid_block_eq' hN hM hj))).symm ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover) (hzdata 0 (Nat.zero_le M))) ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((γ.subpath (τ 0) (τ M)).source.symm.trans
            ((heqUN 0).trans (γ.subpath (vkGrid N j) (vkGrid N (j + 1))).source))) =
        𝟙 _ := by
      rw [CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans]
      exact CategoryTheory.eqToHom_refl _ _
    have hblockM : vkGrid (M * N) (M * j + M) = vkGrid N (j + 1) := by
      rw [show M * j + M = M * (j + 1) from by ring]
      exact vkGrid_block_eq' hN hM hj1
    have hback : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((γ.subpath (vkGrid N j) (vkGrid N (j + 1))).target.symm.trans
            ((heqUN 1).symm.trans (γ.subpath (τ 0) (τ M)).target))) ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          (hzdata M le_rfl)).symm =
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          (congrArg γ hblockM)).symm := by
      rw [CategoryTheory.eqToHom_trans]
    rcases hA j with hUj | hVj
    · have hcellU : γ '' Set.Icc (vkGrid N j) (vkGrid N (j + 1)) ⊆ U := by
        rw [← Path.range_subpath_of_le _ _ _ (vkGrid_mono _ (Nat.le_succ j))]
        exact hUj
      have hWblock : ∀ t, t ≤ M →
          Set.range ⇑(γ.subpath (τ 0) (τ t)) ⊆ U :=
        fun t ht => (hsub_cell t ht).trans hcellU
      have htele := vkTelescope_U F_U F_V hCompat hCover γ τ hτmono hsτ M hWblock
      have hloc := vkLoc_congr F_U F_V hCompat hCover
        (Or.inl (hWblock M le_rfl)) (hA j) heqUN
      calc vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid (M * N) k))
              (fun k => γ.subpath (vkGrid (M * N) k) (vkGrid (M * N) (k + 1)))
              (fun k => hANM k) (M * j + M)
          = ((eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ vkGrid_zero_eq)) ≫
              vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
                (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
                (fun k => hA k) j ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ (vkGrid_block_eq' hN hM hj))).symm)) ≫
            (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (hzdata 0 (Nat.zero_le M))) ≫
              (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                  ((γ.subpath (τ 0) (τ M)).source.symm.trans
                    ((heqUN 0).trans
                      (γ.subpath (vkGrid N j) (vkGrid N (j + 1))).source))) ≫
                vkLoc F_U F_V hCompat hCover
                  (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j) ≫
                eqToHom (congrArg (vkObj0 F_U F_V hCover)
                  ((γ.subpath (vkGrid N j) (vkGrid N (j + 1))).target.symm.trans
                    ((heqUN 1).symm.trans (γ.subpath (τ 0) (τ M)).target))) ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (hzdata M le_rfl)).symm)) := by
            rw [happ, ihm, hbridge, htele, hloc]
            simp only [Category.assoc]
        _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ vkGrid_zero_eq)) ≫
            vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) j ≫
            ((eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ (vkGrid_block_eq' hN hM hj))).symm ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (hzdata 0 (Nat.zero_le M))) ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                ((γ.subpath (τ 0) (τ M)).source.symm.trans
                  ((heqUN 0).trans
                    (γ.subpath (vkGrid N j) (vkGrid N (j + 1))).source)))) ≫
              (vkLoc F_U F_V hCompat hCover
                (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j) ≫
                (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                    ((γ.subpath (vkGrid N j) (vkGrid N (j + 1))).target.symm.trans
                      ((heqUN 1).symm.trans (γ.subpath (τ 0) (τ M)).target))) ≫
                  eqToHom (congrArg (vkObj0 F_U F_V hCover)
                    (hzdata M le_rfl)).symm))) := by
            simp only [Category.assoc]
        _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ vkGrid_zero_eq)) ≫
            vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) j ≫
            (vkLoc F_U F_V hCompat hCover
              (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j) ≫
              (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                  ((γ.subpath (vkGrid N j) (vkGrid N (j + 1))).target.symm.trans
                    ((heqUN 1).symm.trans (γ.subpath (τ 0) (τ M)).target))) ≫
                eqToHom (congrArg (vkObj0 F_U F_V hCover)
                  (hzdata M le_rfl)).symm)) := by
            rw [hmid, Category.id_comp]
        _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ vkGrid_zero_eq)) ≫
            vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) j ≫
            (vkLoc F_U F_V hCompat hCover
              (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j) ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ hblockM)).symm) := by
            rw [hback]
        _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ vkGrid_zero_eq)) ≫
            (vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) j ≫
              vkLoc F_U F_V hCompat hCover
                (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j)) ≫
            eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ hblockM)).symm := by
            simp only [Category.assoc]
    · have hcellV : γ '' Set.Icc (vkGrid N j) (vkGrid N (j + 1)) ⊆ V := by
        rw [← Path.range_subpath_of_le _ _ _ (vkGrid_mono _ (Nat.le_succ j))]
        exact hVj
      have hWblock : ∀ t, t ≤ M →
          Set.range ⇑(γ.subpath (τ 0) (τ t)) ⊆ V :=
        fun t ht => (hsub_cell t ht).trans hcellV
      have htele := vkTelescope_V F_U F_V hCompat hCover γ τ hτmono hsτ M hWblock
      have hloc := vkLoc_congr F_U F_V hCompat hCover
        (Or.inr (hWblock M le_rfl)) (hA j) heqUN
      calc vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid (M * N) k))
              (fun k => γ.subpath (vkGrid (M * N) k) (vkGrid (M * N) (k + 1)))
              (fun k => hANM k) (M * j + M)
          = ((eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ vkGrid_zero_eq)) ≫
              vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
                (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
                (fun k => hA k) j ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ (vkGrid_block_eq' hN hM hj))).symm)) ≫
            (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (hzdata 0 (Nat.zero_le M))) ≫
              (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                  ((γ.subpath (τ 0) (τ M)).source.symm.trans
                    ((heqUN 0).trans
                      (γ.subpath (vkGrid N j) (vkGrid N (j + 1))).source))) ≫
                vkLoc F_U F_V hCompat hCover
                  (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j) ≫
                eqToHom (congrArg (vkObj0 F_U F_V hCover)
                  ((γ.subpath (vkGrid N j) (vkGrid N (j + 1))).target.symm.trans
                    ((heqUN 1).symm.trans (γ.subpath (τ 0) (τ M)).target))) ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (hzdata M le_rfl)).symm)) := by
            rw [happ, ihm, hbridge, htele, hloc]
            simp only [Category.assoc]
        _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ vkGrid_zero_eq)) ≫
            vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) j ≫
            ((eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ (vkGrid_block_eq' hN hM hj))).symm ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (hzdata 0 (Nat.zero_le M))) ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                ((γ.subpath (τ 0) (τ M)).source.symm.trans
                  ((heqUN 0).trans
                    (γ.subpath (vkGrid N j) (vkGrid N (j + 1))).source)))) ≫
              (vkLoc F_U F_V hCompat hCover
                (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j) ≫
                (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                    ((γ.subpath (vkGrid N j) (vkGrid N (j + 1))).target.symm.trans
                      ((heqUN 1).symm.trans (γ.subpath (τ 0) (τ M)).target))) ≫
                  eqToHom (congrArg (vkObj0 F_U F_V hCover)
                    (hzdata M le_rfl)).symm))) := by
            simp only [Category.assoc]
        _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ vkGrid_zero_eq)) ≫
            vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) j ≫
            (vkLoc F_U F_V hCompat hCover
              (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j) ≫
              (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                  ((γ.subpath (vkGrid N j) (vkGrid N (j + 1))).target.symm.trans
                    ((heqUN 1).symm.trans (γ.subpath (τ 0) (τ M)).target))) ≫
                eqToHom (congrArg (vkObj0 F_U F_V hCover)
                  (hzdata M le_rfl)).symm)) := by
            rw [hmid, Category.id_comp]
        _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ vkGrid_zero_eq)) ≫
            vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) j ≫
            (vkLoc F_U F_V hCompat hCover
              (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j) ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ hblockM)).symm) := by
            rw [hback]
        _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ vkGrid_zero_eq)) ≫
            (vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) j ≫
              vkLoc F_U F_V hCompat hCover
                (γ.subpath (vkGrid N j) (vkGrid N (j + 1))) (hA j)) ≫
            eqToHom (congrArg (vkObj0 F_U F_V hCover)
              (congrArg γ hblockM)).symm := by
            simp only [Category.assoc]

/-- A product of numbers `≥ 1` is `≥ 1`. -/
private theorem vkOne_le_mul {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) :
    1 ≤ N * M := by
  calc (1 : ℕ) = 1 * 1 := by ring
  _ ≤ N * M := Nat.mul_le_mul hN hM

/-- Grid independence for `vkChain`: refining the grid `N` by a factor `M`
does not change the value. Follows from `vkGrid_indep_aux` at `j = N` by
merging the endpoint `eqToHom`s. -/
private theorem vkChain_indep {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hA : vkAdm U V γ N) (hANM : vkAdm U V γ (M * N))
    (hMN : 1 ≤ M * N) :
    vkChain F_U F_V hCompat hCover γ (M * N) hMN hANM =
      vkChain F_U F_V hCompat hCover γ N hN hA := by
  have hjN : N ≤ N := le_rfl
  have hAUX := vkGrid_indep_aux F_U F_V hCompat hCover γ N M hN hM hA hANM N hjN
  have hL : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg γ (vkGrid_zero (M * N))).trans γ.source)).symm ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          (congrArg γ vkGrid_zero_eq)) =
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg γ (vkGrid_zero N)).trans γ.source)).symm :=
    CategoryTheory.eqToHom_trans _ _ |>.trans (vkEqToHom_eq _ _)
  have hR : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          (congrArg γ (vkGrid_block_eq' hN hM hjN))).symm ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg γ (vkGrid_top hMN le_rfl)).trans γ.target)) =
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg γ (vkGrid_top hN le_rfl)).trans γ.target)) :=
    CategoryTheory.eqToHom_trans _ _ |>.trans (vkEqToHom_eq _ _)
  have key : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg γ (vkGrid_zero (M * N))).trans γ.source)).symm ≫
        (eqToHom (congrArg (vkObj0 F_U F_V hCover)
            (congrArg γ vkGrid_zero_eq)) ≫
          (vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
              (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
              (fun k => hA k) N ≫
            (eqToHom (congrArg (vkObj0 F_U F_V hCover)
                (congrArg γ (vkGrid_block_eq' hN hM hjN))).symm ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                ((congrArg γ (vkGrid_top hMN le_rfl)).trans γ.target))))) =
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg γ (vkGrid_zero N)).trans γ.source)).symm ≫
        (vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
            (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
            (fun k => hA k) N ≫
          eqToHom (congrArg (vkObj0 F_U F_V hCover)
            ((congrArg γ (vkGrid_top hN le_rfl)).trans γ.target))) := by
    simp only [← Category.assoc]
    rw [hL]
    simp only [Category.assoc]
    rw [hR]
  unfold vkChain
  rw [hAUX]
  simp only [Category.assoc]
  exact key

/-- Grid independence along divisibility: if `N ∣ P` then the `P`-chain equals
the `N`-chain. The divisibility witness is substituted — legal since `P` is a
variable — steering the product into the `M * N` form `vkChain_indep` expects.
-/
private theorem vkChain_dvd {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) (N P : ℕ) (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hdiv : N ∣ P) (hAP : vkAdm U V γ P) (hAN : vkAdm U V γ N) :
    vkChain F_U F_V hCompat hCover γ P hP hAP =
      vkChain F_U F_V hCompat hCover γ N hN hAN := by
  obtain ⟨M, hM⟩ := hdiv
  have hM' : P = M * N := by
    rw [Nat.mul_comm M N]
    exact hM
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · exfalso
      rw [h0, Nat.zero_mul] at hM'
      omega
    · exact hpos
  subst hM'
  exact vkChain_indep F_U F_V hCompat hCover γ N M hN hM1 hAN hAP
    (vkOne_le_mul hM1 hN)

/-- Two admissible grids give the same chain: compare both with `N₁ * N₂`. -/
private theorem vkChain_indep2 {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {a b : X} (γ : Path a b) (N1 N2 : ℕ) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hA1 : vkAdm U V γ N1) (hA2 : vkAdm U V γ N2) :
    vkChain F_U F_V hCompat hCover γ N1 hN1 hA1 =
      vkChain F_U F_V hCompat hCover γ N2 hN2 hA2 := by
  have hA12 : vkAdm U V γ (N1 * N2) := vkAdm_mul hN1 hN2 hA1
  have hP : 1 ≤ N1 * N2 := vkOne_le_mul hN1 hN2
  have e1 := vkChain_dvd F_U F_V hCompat hCover γ N1 (N1 * N2) hN1 hP
    ⟨N2, rfl⟩ hA12 hA1
  have e2 := vkChain_dvd F_U F_V hCompat hCover γ N2 (N1 * N2) hN2 hP
    ⟨N1, Nat.mul_comm _ _⟩ hA12 hA2
  exact e1.symm.trans e2

/-- The path-level value: the grid chain at some admissible grid. -/
private noncomputable def vkPhi {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    {a b : X} (γ : Path a b) :
    vkObj0 F_U F_V hCover a ⟶ vkObj0 F_U F_V hCover b :=
  vkChain F_U F_V hCompat hCover γ
    (Classical.choose (vkLebesgue1D hU hV hCover γ))
    (Classical.choose_spec (vkLebesgue1D hU hV hCover γ)).1
    (Classical.choose_spec (vkLebesgue1D hU hV hCover γ)).2

/-- `Φ` equals the chain at any admissible grid. -/
private theorem vkPhi_eq {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    {a b : X} (γ : Path a b) (N : ℕ) (hN : 1 ≤ N) (hA : vkAdm U V γ N) :
    vkPhi F_U F_V hCompat hCover hU hV γ =
      vkChain F_U F_V hCompat hCover γ N hN hA := by
  unfold vkPhi
  exact vkChain_indep2 F_U F_V hCompat hCover γ _ N
    (Classical.choose_spec (vkLebesgue1D hU hV hCover γ)).1 hN
    (Classical.choose_spec (vkLebesgue1D hU hV hCover γ)).2 hA

/-- Strip lemma: consecutive rows of a subdivided path homotopy have equal grid
chains. Each column strip telescopes by the corner-square lemma applied in the
chart of grid cell `(j, k)`. The row admissibility proofs are supplied by the
caller; smallness of the vertical paths is derived from the cell data. -/
private theorem vkStrip {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    {x y : X} {γ γ' : Path x y} (H : Path.Homotopy γ γ')
    (N : ℕ) (hN : 1 ≤ N) (j : ℕ)
    (hcell : ∀ k, (∀ z ∈ Set.Icc (vkGrid N j) (vkGrid N (j + 1)) ×ˢ
        Set.Icc (vkGrid N k) (vkGrid N (k + 1)), H.toHomotopy z ∈ U) ∨
      (∀ z ∈ Set.Icc (vkGrid N j) (vkGrid N (j + 1)) ×ˢ
        Set.Icc (vkGrid N k) (vkGrid N (k + 1)), H.toHomotopy z ∈ V))
    (hAρ : vkAdm U V (H.eval (vkGrid N j)) N)
    (hAρ' : vkAdm U V (H.eval (vkGrid N (j + 1))) N) :
    vkChain F_U F_V hCompat hCover (H.eval (vkGrid N j)) N hN hAρ =
      vkChain F_U F_V hCompat hCover (H.eval (vkGrid N (j + 1))) N hN hAρ' := by
  have hss' : vkGrid N j ≤ vkGrid N (j + 1) := vkGrid_mono _ (Nat.le_succ j)
  have hρapp : ∀ t : ↥unitInterval,
      H.eval (vkGrid N j) t = H.toHomotopy (vkGrid N j, t) := fun t => rfl
  have hρapp' : ∀ t : ↥unitInterval,
      H.eval (vkGrid N (j + 1)) t = H.toHomotopy (vkGrid N (j + 1), t) :=
    fun t => rfl
  have hsubρ : ∀ (p q w : ↥unitInterval),
      ((H.eval (vkGrid N j)).subpath p q) w =
        H.eval (vkGrid N j) (Set.Icc.convexComb p q w : ↥unitInterval) :=
    fun p q w => rfl
  have hsubρ' : ∀ (p q w : ↥unitInterval),
      ((H.eval (vkGrid N (j + 1))).subpath p q) w =
        H.eval (vkGrid N (j + 1)) (Set.Icc.convexComb p q w : ↥unitInterval) :=
    fun p q w => rfl
  have hνinner : ∀ k, Continuous (fun u : ↥unitInterval =>
      (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) u, vkGrid N k)) := by
    intro k
    fun_prop
  set ν : (k : ℕ) → Path (H.eval (vkGrid N j) (vkGrid N k))
      (H.eval (vkGrid N (j + 1)) (vkGrid N k)) := fun k =>
    { toFun := fun u => H.toHomotopy
        (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) u, vkGrid N k)
      continuous_toFun := H.toHomotopy.continuous.comp (hνinner k)
      source' := by
        rw [Set.Icc.convexComb_zero]
        exact (hρapp _).symm
      target' := by
        rw [Set.Icc.convexComb_one]
        exact (hρapp' _).symm } with hνdef
  have hνapp : ∀ (k : ℕ) (u : ↥unitInterval), ν k u = H.toHomotopy
      (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) u, vkGrid N k) :=
    fun k u => rfl
  have hνsmall : ∀ k, vkSmall U V (ν k) := by
    intro k
    rcases hcell k with hU | hV
    · left
      intro y hy
      obtain ⟨u, rfl⟩ := hy
      rw [hνapp k u]
      exact hU _ (Set.mk_mem_prod
        (Set.mem_Icc.mpr ⟨Set.Icc.le_convexComb hss' u,
          Set.Icc.convexComb_le hss' u⟩)
        (Set.mem_Icc.mpr ⟨le_rfl, vkGrid_mono _ (Nat.le_succ k)⟩))
    · right
      intro y hy
      obtain ⟨u, rfl⟩ := hy
      rw [hνapp k u]
      exact hV _ (Set.mk_mem_prod
        (Set.mem_Icc.mpr ⟨Set.Icc.le_convexComb hss' u,
          Set.Icc.convexComb_le hss' u⟩)
        (Set.mem_Icc.mpr ⟨le_rfl, vkGrid_mono _ (Nat.le_succ k)⟩))
  have Q : ∀ k, vkLoc F_U F_V hCompat hCover (ν 0) (hνsmall 0) ≫
      vkChainSeq F_U F_V hCompat hCover
        (fun k => H.eval (vkGrid N (j + 1)) (vkGrid N k))
        (fun k => (H.eval (vkGrid N (j + 1))).subpath (vkGrid N k)
          (vkGrid N (k + 1)))
        (fun k => hAρ' k) k =
      vkChainSeq F_U F_V hCompat hCover
        (fun k => H.eval (vkGrid N j) (vkGrid N k))
        (fun k => (H.eval (vkGrid N j)).subpath (vkGrid N k) (vkGrid N (k + 1)))
        (fun k => hAρ k) k ≫
      vkLoc F_U F_V hCompat hCover (ν k) (hνsmall k) := by
    intro k
    induction k with
    | zero =>
      rw [vkChainSeq_zero, vkChainSeq_zero]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    | succ k ih =>
      rcases hcell k with hcellU | hcellV
      · have hinner : Continuous (fun p : ↥unitInterval × ↥unitInterval =>
          (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) p.1,
           Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) p.2)) := by
          fun_prop
        set g : C(↥unitInterval × ↥unitInterval, X) :=
          ⟨fun p => H.toHomotopy
            (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) p.1,
             Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) p.2),
            H.toHomotopy.continuous.comp hinner⟩ with hgdef
        have hg_eq : ∀ u v : ↥unitInterval, g (u, v) = H.toHomotopy
            (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) u,
             Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) v) :=
          fun u v => rfl
        have hgU : ∀ z : ↥unitInterval × ↥unitInterval, g z ∈ U := by
          intro z
          obtain ⟨u, v⟩ := z
          rw [hg_eq u v]
          exact hcellU _ (Set.mk_mem_prod
            (Set.mem_Icc.mpr ⟨Set.Icc.le_convexComb hss' u,
              Set.Icc.convexComb_le hss' u⟩)
            (Set.mem_Icc.mpr ⟨Set.Icc.le_convexComb
              (vkGrid_mono _ (Nat.le_succ k)) v,
              Set.Icc.convexComb_le (vkGrid_mono _ (Nat.le_succ k)) v⟩))
        have hbot : ∀ u : ↥unitInterval, ν k u = g (u, 0) := by
          intro u
          rw [hνapp k u, hg_eq u 0, Set.Icc.convexComb_zero]
        have hrgt : ∀ v : ↥unitInterval,
            ((H.eval (vkGrid N (j + 1))).subpath (vkGrid N k)
              (vkGrid N (k + 1))) v = g (1, v) := by
          intro v
          rw [hsubρ' _ _ v, hρapp' _, hg_eq 1 v, Set.Icc.convexComb_one]
        have hlft : ∀ v : ↥unitInterval,
            ((H.eval (vkGrid N j)).subpath (vkGrid N k)
              (vkGrid N (k + 1))) v = g (0, v) := by
          intro v
          rw [hsubρ _ _ v, hρapp _, hg_eq 0 v, Set.Icc.convexComb_zero]
        have htop : ∀ u : ↥unitInterval, ν (k + 1) u = g (u, 1) := by
          intro u
          rw [hνapp (k + 1) u, hg_eq u 1, Set.Icc.convexComb_one]
        have hsq := vkLoc_square_U F_U F_V hCompat hCover g hgU
          (ν k)
          ((H.eval (vkGrid N (j + 1))).subpath (vkGrid N k) (vkGrid N (k + 1)))
          ((H.eval (vkGrid N j)).subpath (vkGrid N k) (vkGrid N (k + 1)))
          (ν (k + 1))
          (hνsmall k) (hAρ' k) (hAρ k) (hνsmall (k + 1))
          hbot hrgt hlft htop
        rw [vkChainSeq_succ, vkChainSeq_succ]
        rw [← Category.assoc, ih, Category.assoc, hsq, Category.assoc]
      · have hinner : Continuous (fun p : ↥unitInterval × ↥unitInterval =>
          (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) p.1,
           Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) p.2)) := by
          fun_prop
        set g : C(↥unitInterval × ↥unitInterval, X) :=
          ⟨fun p => H.toHomotopy
            (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) p.1,
             Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) p.2),
            H.toHomotopy.continuous.comp hinner⟩ with hgdef
        have hg_eq : ∀ u v : ↥unitInterval, g (u, v) = H.toHomotopy
            (Set.Icc.convexComb (vkGrid N j) (vkGrid N (j + 1)) u,
             Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) v) :=
          fun u v => rfl
        have hgV : ∀ z : ↥unitInterval × ↥unitInterval, g z ∈ V := by
          intro z
          obtain ⟨u, v⟩ := z
          rw [hg_eq u v]
          exact hcellV _ (Set.mk_mem_prod
            (Set.mem_Icc.mpr ⟨Set.Icc.le_convexComb hss' u,
              Set.Icc.convexComb_le hss' u⟩)
            (Set.mem_Icc.mpr ⟨Set.Icc.le_convexComb
              (vkGrid_mono _ (Nat.le_succ k)) v,
              Set.Icc.convexComb_le (vkGrid_mono _ (Nat.le_succ k)) v⟩))
        have hbot : ∀ u : ↥unitInterval, ν k u = g (u, 0) := by
          intro u
          rw [hνapp k u, hg_eq u 0, Set.Icc.convexComb_zero]
        have hrgt : ∀ v : ↥unitInterval,
            ((H.eval (vkGrid N (j + 1))).subpath (vkGrid N k)
              (vkGrid N (k + 1))) v = g (1, v) := by
          intro v
          rw [hsubρ' _ _ v, hρapp' _, hg_eq 1 v, Set.Icc.convexComb_one]
        have hlft : ∀ v : ↥unitInterval,
            ((H.eval (vkGrid N j)).subpath (vkGrid N k)
              (vkGrid N (k + 1))) v = g (0, v) := by
          intro v
          rw [hsubρ _ _ v, hρapp _, hg_eq 0 v, Set.Icc.convexComb_zero]
        have htop : ∀ u : ↥unitInterval, ν (k + 1) u = g (u, 1) := by
          intro u
          rw [hνapp (k + 1) u, hg_eq u 1, Set.Icc.convexComb_one]
        have hsq := vkLoc_square_V F_U F_V hCompat hCover g hgV
          (ν k)
          ((H.eval (vkGrid N (j + 1))).subpath (vkGrid N k) (vkGrid N (k + 1)))
          ((H.eval (vkGrid N j)).subpath (vkGrid N k) (vkGrid N (k + 1)))
          (ν (k + 1))
          (hνsmall k) (hAρ' k) (hAρ k) (hνsmall (k + 1))
          hbot hrgt hlft htop
        rw [vkChainSeq_succ, vkChainSeq_succ]
        rw [← Category.assoc, ih, Category.assoc, hsq, Category.assoc]
  have hν0const : ∀ u : ↥unitInterval, ν 0 u = x := by
    intro u
    rw [hνapp 0 u, vkGrid_zero N]
    exact H.source _
  have hνNconst : ∀ u : ↥unitInterval, ν N u = y := by
    intro u
    rw [hνapp N u, vkGrid_top hN le_rfl]
    exact H.target _
  have hρx : H.eval (vkGrid N j) (vkGrid N 0) = x := by
    rw [hρapp (vkGrid N 0), vkGrid_zero N]
    exact H.source _
  have hρy : H.eval (vkGrid N j) (vkGrid N N) = y := by
    rw [hρapp (vkGrid N N), vkGrid_top hN le_rfl]
    exact H.target _
  have hconst0 : ∀ u : ↥unitInterval,
      ν 0 u = H.eval (vkGrid N j) (vkGrid N 0) :=
    fun u => (hν0const u).trans hρx.symm
  have hconstN : ∀ u : ↥unitInterval,
      ν N u = H.eval (vkGrid N j) (vkGrid N N) :=
    fun u => (hνNconst u).trans hρy.symm
  have hν0 : vkLoc F_U F_V hCompat hCover (ν 0) (hνsmall 0) =
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((hconst0 1).symm.trans (ν 0).target)) :=
    vkLoc_const F_U F_V hCompat hCover (hνsmall 0) hconst0
  have hνN : vkLoc F_U F_V hCompat hCover (ν N) (hνsmall N) =
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((hconstN 1).symm.trans (ν N).target)) :=
    vkLoc_const F_U F_V hCompat hCover (hνsmall N) hconstN
  have hinv0 : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((hconst0 1).symm.trans (ν 0).target)).symm ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((hconst0 1).symm.trans (ν 0).target)) = 𝟙 _ :=
    (CategoryTheory.eqToHom_trans _ _).trans
      (CategoryTheory.eqToHom_refl _ _)
  have hchain' : vkChainSeq F_U F_V hCompat hCover
        (fun k => H.eval (vkGrid N (j + 1)) (vkGrid N k))
        (fun k => (H.eval (vkGrid N (j + 1))).subpath (vkGrid N k)
          (vkGrid N (k + 1)))
        (fun k => hAρ' k) N =
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((hconst0 1).symm.trans (ν 0).target)).symm ≫
        vkChainSeq F_U F_V hCompat hCover
          (fun k => H.eval (vkGrid N j) (vkGrid N k))
          (fun k => (H.eval (vkGrid N j)).subpath (vkGrid N k)
            (vkGrid N (k + 1)))
          (fun k => hAρ k) N ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((hconstN 1).symm.trans (ν N).target)) := by
    have QN := Q N
    rw [hν0, hνN] at QN
    calc vkChainSeq F_U F_V hCompat hCover
            (fun k => H.eval (vkGrid N (j + 1)) (vkGrid N k))
            (fun k => (H.eval (vkGrid N (j + 1))).subpath (vkGrid N k)
              (vkGrid N (k + 1)))
            (fun k => hAρ' k) N
        = eqToHom (congrArg (vkObj0 F_U F_V hCover)
            ((hconst0 1).symm.trans (ν 0).target)).symm ≫
            (eqToHom (congrArg (vkObj0 F_U F_V hCover)
              ((hconst0 1).symm.trans (ν 0).target)) ≫
              vkChainSeq F_U F_V hCompat hCover
                (fun k => H.eval (vkGrid N (j + 1)) (vkGrid N k))
                (fun k => (H.eval (vkGrid N (j + 1))).subpath (vkGrid N k)
                  (vkGrid N (k + 1)))
                (fun k => hAρ' k) N) := by
          rw [← Category.assoc, hinv0, Category.id_comp]
      _ = eqToHom (congrArg (vkObj0 F_U F_V hCover)
            ((hconst0 1).symm.trans (ν 0).target)).symm ≫
            (vkChainSeq F_U F_V hCompat hCover
              (fun k => H.eval (vkGrid N j) (vkGrid N k))
              (fun k => (H.eval (vkGrid N j)).subpath (vkGrid N k)
                (vkGrid N (k + 1)))
              (fun k => hAρ k) N ≫
              eqToHom (congrArg (vkObj0 F_U F_V hCover)
                ((hconstN 1).symm.trans (ν N).target))) := by
          rw [QN]
  have mL : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg (H.eval (vkGrid N (j + 1))) (vkGrid_zero N)).trans
            (H.eval (vkGrid N (j + 1))).source)).symm ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((hconst0 1).symm.trans (ν 0).target)).symm =
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg (H.eval (vkGrid N j)) (vkGrid_zero N)).trans
            (H.eval (vkGrid N j)).source)).symm :=
    (CategoryTheory.eqToHom_trans _ _).trans (vkEqToHom_eq _ _)
  have mR : eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((hconstN 1).symm.trans (ν N).target)) ≫
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg (H.eval (vkGrid N (j + 1))) (vkGrid_top hN le_rfl)).trans
            (H.eval (vkGrid N (j + 1))).target)) =
        eqToHom (congrArg (vkObj0 F_U F_V hCover)
          ((congrArg (H.eval (vkGrid N j)) (vkGrid_top hN le_rfl)).trans
            (H.eval (vkGrid N j)).target)) :=
    (CategoryTheory.eqToHom_trans _ _).trans (vkEqToHom_eq _ _)
  unfold vkChain
  rw [hchain']
  simp only [← Category.assoc]
  rw [mL]
  simp only [Category.assoc]
  rw [mR]

/-- Rows of a subdivided path homotopy are admissible grids: each row piece
lies in a grid cell. -/
private theorem vkRow_adm {X : Type*} [TopologicalSpace X] {U V : Set X}
    {x y : X} {γ γ' : Path x y} (H : Path.Homotopy γ γ')
    (N : ℕ) (j : ℕ)
    (hcell : ∀ i k, (∀ z ∈ Set.Icc (vkGrid N i) (vkGrid N (i + 1)) ×ˢ
        Set.Icc (vkGrid N k) (vkGrid N (k + 1)), H.toHomotopy z ∈ U) ∨
      (∀ z ∈ Set.Icc (vkGrid N i) (vkGrid N (i + 1)) ×ˢ
        Set.Icc (vkGrid N k) (vkGrid N (k + 1)), H.toHomotopy z ∈ V)) :
    vkAdm U V (H.eval (vkGrid N j)) N := by
  have hρapp : ∀ t : ↥unitInterval,
      H.eval (vkGrid N j) t = H.toHomotopy (vkGrid N j, t) := fun t => rfl
  intro k
  have hkle : vkGrid N k ≤ vkGrid N (k + 1) := vkGrid_mono _ (Nat.le_succ k)
  have hmemj : vkGrid N j ∈ Set.Icc (vkGrid N j) (vkGrid N (j + 1)) :=
    Set.mem_Icc.mpr ⟨le_rfl, vkGrid_mono _ (Nat.le_succ j)⟩
  rcases hcell j k with hU | hV
  · left
    rw [Path.range_subpath_of_le _ _ _ hkle]
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    rw [hρapp t]
    exact hU _ (Set.mk_mem_prod hmemj ht)
  · right
    rw [Path.range_subpath_of_le _ _ _ hkle]
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    rw [hρapp t]
    exact hV _ (Set.mk_mem_prod hmemj ht)

/-- `Φ` is invariant under path homotopy: subdivide the homotopy square and
telescope row by row. -/
private theorem vkPhi_homotopy_invariant {X : Type*} [TopologicalSpace X]
    {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    {x y : X} {γ γ' : Path x y} (hhom : γ.Homotopic γ') :
    vkPhi F_U F_V hCompat hCover hU hV γ =
      vkPhi F_U F_V hCompat hCover hU hV γ' := by
  obtain ⟨H⟩ := hhom
  obtain ⟨N, hN, hcell⟩ := vkLebesgue2D hU hV hCover H.toHomotopy
  have e0 : H.eval (vkGrid N 0) = γ := by
    rw [vkGrid_zero, Path.Homotopy.eval_zero]
  have eN : H.eval (vkGrid N N) = γ' := by
    rw [vkGrid_top hN le_rfl, Path.Homotopy.eval_one]
  have hrows : ∀ j, vkAdm U V (H.eval (vkGrid N j)) N :=
    fun j => vkRow_adm H N j hcell
  have Q : ∀ j, j ≤ N → vkChain F_U F_V hCompat hCover
        (H.eval (vkGrid N 0)) N hN (hrows 0) =
      vkChain F_U F_V hCompat hCover (H.eval (vkGrid N j)) N hN (hrows j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rfl
    | succ j ih =>
      intro hj1
      have hj : j ≤ N := Nat.le_of_succ_le hj1
      have step := vkStrip F_U F_V hCompat hCover H N hN j
        (fun k => hcell j k) (hrows j) (hrows (j + 1))
      calc vkChain F_U F_V hCompat hCover (H.eval (vkGrid N 0)) N hN (hrows 0)
          = vkChain F_U F_V hCompat hCover (H.eval (vkGrid N j)) N hN
            (hrows j) := ih hj
        _ = vkChain F_U F_V hCompat hCover (H.eval (vkGrid N (j + 1))) N hN
            (hrows (j + 1)) := step
  have QN := Q N le_rfl
  have eL := vkPhi_eq F_U F_V hCompat hCover hU hV (H.eval (vkGrid N 0)) N hN
    (hrows 0)
  have eR := vkPhi_eq F_U F_V hCompat hCover hU hV (H.eval (vkGrid N N)) N hN
    (hrows N)
  calc vkPhi F_U F_V hCompat hCover hU hV γ
      = vkPhi F_U F_V hCompat hCover hU hV (H.eval (vkGrid N 0)) :=
        congrArg _ e0.symm
    _ = vkChain F_U F_V hCompat hCover (H.eval (vkGrid N 0)) N hN (hrows 0) :=
        eL
    _ = vkChain F_U F_V hCompat hCover (H.eval (vkGrid N N)) N hN (hrows N) :=
        QN
    _ = vkPhi F_U F_V hCompat hCover hU hV (H.eval (vkGrid N N)) := eR.symm
    _ = vkPhi F_U F_V hCompat hCover hU hV γ' := congrArg _ eN

/-- Any round trip of `eqToHom`s is the identity. -/
private theorem vkEqToHom_loop {C : Type*} [Category C] {X Y : C}
    (h1 : X = Y) (h2 : Y = X) :
    eqToHom h1 ≫ eqToHom h2 = 𝟙 _ := by
  cases h1
  cases h2
  simp

/-- `Φ` of a small path is `loc`. Grid `1` is admissible since every
subpath range lies in the range of `p`; the length-one chain is `loc` of the
`(0, 1)`-subpath, which is pointwise `p`. -/
private theorem vkPhi_small {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    {a b : X} (p : Path a b) (hs : vkSmall U V p) :
    vkPhi F_U F_V hCompat hCover hU hV p =
      vkLoc F_U F_V hCompat hCover p hs := by
  have hsub : ∀ (s t : ↥unitInterval),
      Set.range ⇑(p.subpath s t) ⊆ Set.range ⇑p := by
    intro s t y hy
    obtain ⟨u, rfl⟩ := hy
    exact ⟨Set.Icc.convexComb s t u, rfl⟩
  have hA : vkAdm U V p 1 := by
    intro k
    rcases hs with hU' | hV'
    · left
      exact (hsub _ _).trans hU'
    · right
      exact (hsub _ _).trans hV'
  rw [vkPhi_eq F_U F_V hCompat hCover hU hV p 1 le_rfl hA]
  have heq : ∀ s : ↥unitInterval,
      (p.subpath (vkGrid 1 0) (vkGrid 1 1)) s = p s := by
    intro s
    have e : (p.subpath (vkGrid 1 0) (vkGrid 1 1)) s =
        p (Set.Icc.convexComb (vkGrid 1 0) (vkGrid 1 1) s :
          ↥unitInterval) := rfl
    rw [e, vkGrid_zero, vkGrid_top le_rfl le_rfl,
      Set.Icc.convexComb_zero_one]
  have hc := hs
  rcases hc with hUcover | hVcover
  · have hW : ∀ j, j ≤ 1 →
        Set.range ⇑(p.subpath (vkGrid 1 0) (vkGrid 1 j)) ⊆ U :=
      fun j _ => (hsub _ _).trans hUcover
    have htele := vkTelescope_U F_U F_V hCompat hCover p (fun k => vkGrid 1 k)
      (vkGrid_mono 1) (fun k => hA k) 1 hW
    have hloc := vkLoc_congr F_U F_V hCompat hCover (Or.inl (hW 1 le_rfl)) hs heq
    unfold vkChain
    rw [htele, hloc]
    simp only [Category.assoc]
    rw [vkEqToHom_loop, Category.comp_id, ← Category.assoc, vkEqToHom_loop,
      Category.id_comp]
  · have hW : ∀ j, j ≤ 1 →
        Set.range ⇑(p.subpath (vkGrid 1 0) (vkGrid 1 j)) ⊆ V :=
      fun j _ => (hsub _ _).trans hVcover
    have htele := vkTelescope_V F_U F_V hCompat hCover p (fun k => vkGrid 1 k)
      (vkGrid_mono 1) (fun k => hA k) 1 hW
    have hloc := vkLoc_congr F_U F_V hCompat hCover (Or.inr (hW 1 le_rfl)) hs heq
    unfold vkChain
    rw [htele, hloc]
    simp only [Category.assoc]
    rw [vkEqToHom_loop, Category.comp_id, ← Category.assoc, vkEqToHom_loop,
      Category.id_comp]

/-- `Φ` of a constant path is the identity. -/
private theorem vkPhi_refl {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    (x : X) :
    vkPhi F_U F_V hCompat hCover hU hV (Path.refl x) = 𝟙 _ := by
  have hxU : x ∈ U ∪ V := by
    rw [hCover]
    exact Set.mem_univ x
  have hs : vkSmall U V (Path.refl x) := by
    rcases hxU with hUx | hVx
    · left
      intro y hy
      obtain ⟨u, rfl⟩ := hy
      exact hUx
    · right
      intro y hy
      obtain ⟨u, rfl⟩ := hy
      exact hVx
  rw [vkPhi_small F_U F_V hCompat hCover hU hV (Path.refl x) hs]
  have hc := vkLoc_const F_U F_V hCompat hCover hs (fun u => rfl)
  rw [hc]
  exact CategoryTheory.eqToHom_refl _ _

/-- Helper: `(γ.trans γ') t = γ' (2t - 1)` for `t ≥ 1/2`. -/
private theorem vkTrans_apply_ge {X : Type*} [TopologicalSpace X]
    {x y z : X} (γ : Path x y) (γ' : Path y z) (t : ↥unitInterval)
    (ht : (1 / 2 : ℝ) ≤ (t : ℝ)) :
    (γ.trans γ') t = γ' ⟨2 * (t : ℝ) - 1, by
      constructor
      · linarith [t.2.1]
      · linarith [t.2.2]⟩ := by
  have hT := Path.trans_apply γ γ' t
  rw [hT]
  split_ifs with h
  · have hte : (t : ℝ) = 1 / 2 := le_antisymm h ht
    have e1 : (⟨2 * (t : ℝ), by
        have h0 : (0 : ℝ) ≤ 2 * (t : ℝ) := by linarith [t.2.1]
        have h1 : 2 * (t : ℝ) ≤ 1 := by linarith [hte]
        exact ⟨h0, h1⟩⟩ : ↥unitInterval) = 1 := by
      apply Subtype.ext
      change 2 * (t : ℝ) = ((1 : ↥unitInterval) : ℝ)
      rw [hte]
      norm_num
    have e0 : (⟨2 * (t : ℝ) - 1, by
        constructor
        · linarith [t.2.1]
        · linarith [t.2.2]⟩ : ↥unitInterval) = 0 := by
      apply Subtype.ext
      change 2 * (t : ℝ) - 1 = ((0 : ↥unitInterval) : ℝ)
      rw [hte]
      norm_num
    calc γ ⟨2 * (t : ℝ), by
            have h0 : (0 : ℝ) ≤ 2 * (t : ℝ) := by linarith [t.2.1]
            have h1 : 2 * (t : ℝ) ≤ 1 := by linarith [hte]
            exact ⟨h0, h1⟩⟩
        = γ 1 := congrArg γ e1
      _ = y := γ.target
      _ = γ' 0 := γ'.source.symm
      _ = γ' ⟨2 * (t : ℝ) - 1, by
            constructor
            · linarith [t.2.1]
            · linarith [t.2.2]⟩ := congrArg γ' e0.symm
  · rfl

/-- Helper: `(γ.trans γ') t = γ (2t)` for `t ≤ 1/2`. -/
private theorem vkTrans_apply_le {X : Type*} [TopologicalSpace X]
    {x y z : X} (γ : Path x y) (γ' : Path y z) (t : ↥unitInterval)
    (ht : (t : ℝ) ≤ (1 / 2 : ℝ)) :
    (γ.trans γ') t = γ ⟨2 * (t : ℝ), by
      constructor
      · linarith [t.2.1]
      · linarith [ht, t.2.1]⟩ := by
  have hT := Path.trans_apply γ γ' t
  rw [hT, dite_eq_left ht]

/-- Grid points of the doubled grid in the first half lie below `1/2`. -/
private theorem vkGrid_le_half {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    ((vkGrid (2 * N) k : ↥unitInterval) : ℝ) ≤ 1 / 2 := by
  have h2N : 1 ≤ 2 * N := by omega
  have hkle : k ≤ 2 * N := by omega
  rw [vkGrid_val_of_le h2N hkle]
  have hpos : (0 : ℝ) < ((((2 * N : ℕ))) : ℝ) := by
    have h : 0 < 2 * N := by omega
    exact_mod_cast h
  have hkR : ((k : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hk
  have e : (1 / 2 : ℝ) * ((((2 * N : ℕ))) : ℝ) = (((N : ℕ)) : ℝ) := by
    push_cast
    ring
  rw [div_le_iff₀ hpos, e]
  exact hkR

/-- Grid points of the doubled grid in the second half lie above `1/2`. -/
private theorem vkGrid_half_le {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    (1 / 2 : ℝ) ≤ ((vkGrid (2 * N) (N + k) : ↥unitInterval) : ℝ) := by
  have h2N : 1 ≤ 2 * N := by omega
  have hkle : N + k ≤ 2 * N := by omega
  rw [vkGrid_val_of_le h2N hkle]
  have hpos : (0 : ℝ) < ((((2 * N : ℕ))) : ℝ) := by
    have h : 0 < 2 * N := by omega
    exact_mod_cast h
  have hkR : (((N : ℕ)) : ℝ) ≤ (((N + k : ℕ)) : ℝ) := by
    exact_mod_cast Nat.le_add_right N k
  have e : (1 / 2 : ℝ) * ((((2 * N : ℕ))) : ℝ) = (((N : ℕ)) : ℝ) := by
    push_cast
    ring
  rw [le_div_iff₀ hpos, e]
  exact hkR

/-- Doubling commutes with convex combinations in the first half. -/
private theorem vkConvexComb_double_fst {N k : ℕ} (hN : 1 ≤ N) (hk : k < N)
    (s : ↥unitInterval) :
    2 * ((Set.Icc.convexComb (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1)) s :
      ↥unitInterval) : ℝ) =
      ((Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) s :
        ↥unitInterval) : ℝ) := by
  have d1 := vkGrid_double_fst hN (show k ≤ N by omega)
  have d2 := vkGrid_double_fst hN (show k + 1 ≤ N by omega)
  simp only [Set.Icc.coe_convexComb]
  linear_combination (1 - (s : ℝ)) * d1 + (s : ℝ) * d2

/-- Doubling commutes with convex combinations in the second half. -/
private theorem vkConvexComb_double_snd {N k : ℕ} (hN : 1 ≤ N) (hk : k < N)
    (s : ↥unitInterval) :
    2 * ((Set.Icc.convexComb (vkGrid (2 * N) (N + k)) (vkGrid (2 * N) (N + k + 1))
      s : ↥unitInterval) : ℝ) - 1 =
      ((Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) s :
        ↥unitInterval) : ℝ) := by
  have d1 := vkGrid_double_snd hN (show k ≤ N by omega)
  have d2 := vkGrid_double_snd hN (show k + 1 ≤ N by omega)
  rw [show N + (k + 1) = N + k + 1 from by omega] at d2
  simp only [Set.Icc.coe_convexComb]
  linear_combination (1 - (s : ℝ)) * d1 + (s : ℝ) * d2

/-- Pieces of the concatenated path in the first half agree pointwise with
pieces of the first path. -/
private theorem vkTrans_piece_fst {X : Type*} [TopologicalSpace X]
    {x y z : X} (γ : Path x y) (γ' : Path y z)
    {N k : ℕ} (hN : 1 ≤ N) (hk : k < N) (s : ↥unitInterval) :
    ((γ.trans γ').subpath (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1))) s =
      (γ.subpath (vkGrid N k) (vkGrid N (k + 1))) s := by
  have hmono : vkGrid (2 * N) k ≤ vkGrid (2 * N) (k + 1) :=
    vkGrid_mono _ (Nat.le_succ k)
  have hle : ((Set.Icc.convexComb (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1)) s :
      ↥unitInterval) : ℝ) ≤ 1 / 2 := by
    have h1 : Set.Icc.convexComb (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1)) s ≤
        vkGrid (2 * N) (k + 1) :=
      Set.Icc.convexComb_le hmono s
    have h2 : ((vkGrid (2 * N) (k + 1) : ↥unitInterval) : ℝ) ≤ 1 / 2 :=
      vkGrid_le_half hN (by omega)
    calc ((Set.Icc.convexComb (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1)) s :
            ↥unitInterval) : ℝ)
        ≤ ((vkGrid (2 * N) (k + 1) : ↥unitInterval) : ℝ) := by
          exact_mod_cast h1
      _ ≤ 1 / 2 := h2
  have hval : 2 * ((Set.Icc.convexComb (vkGrid (2 * N) k)
      (vkGrid (2 * N) (k + 1)) s : ↥unitInterval) : ℝ) =
      ((Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) s :
        ↥unitInterval) : ℝ) :=
    vkConvexComb_double_fst hN hk s
  calc ((γ.trans γ').subpath (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1))) s
      = (γ.trans γ') (Set.Icc.convexComb (vkGrid (2 * N) k)
        (vkGrid (2 * N) (k + 1)) s) := rfl
    _ = γ (Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) s) := by
        rw [vkTrans_apply_le _ _ _ hle]
        congr 1
        exact Subtype.ext hval
    _ = (γ.subpath (vkGrid N k) (vkGrid N (k + 1))) s := rfl

/-- Pieces of the concatenated path in the second half agree pointwise with
pieces of the second path. -/
private theorem vkTrans_piece_snd {X : Type*} [TopologicalSpace X]
    {x y z : X} (γ : Path x y) (γ' : Path y z)
    {N k : ℕ} (hN : 1 ≤ N) (hk : k < N) (s : ↥unitInterval) :
    ((γ.trans γ').subpath (vkGrid (2 * N) (N + k)) (vkGrid (2 * N) (N + k + 1))) s =
      (γ'.subpath (vkGrid N k) (vkGrid N (k + 1))) s := by
  have hmono : vkGrid (2 * N) (N + k) ≤ vkGrid (2 * N) (N + k + 1) :=
    vkGrid_mono _ (Nat.le_succ _)
  have hge : (1 / 2 : ℝ) ≤ ((Set.Icc.convexComb (vkGrid (2 * N) (N + k))
      (vkGrid (2 * N) (N + k + 1)) s : ↥unitInterval) : ℝ) := by
    have h1 : vkGrid (2 * N) (N + k) ≤
        Set.Icc.convexComb (vkGrid (2 * N) (N + k)) (vkGrid (2 * N) (N + k + 1)) s :=
      Set.Icc.le_convexComb hmono s
    have h2 : (1 / 2 : ℝ) ≤ ((vkGrid (2 * N) (N + k) : ↥unitInterval) : ℝ) :=
      vkGrid_half_le hN (by omega)
    calc (1 / 2 : ℝ)
        ≤ ((vkGrid (2 * N) (N + k) : ↥unitInterval) : ℝ) := h2
      _ ≤ ((Set.Icc.convexComb (vkGrid (2 * N) (N + k))
          (vkGrid (2 * N) (N + k + 1)) s : ↥unitInterval) : ℝ) := by
          exact_mod_cast h1
  have hval : 2 * ((Set.Icc.convexComb (vkGrid (2 * N) (N + k))
      (vkGrid (2 * N) (N + k + 1)) s : ↥unitInterval) : ℝ) - 1 =
      ((Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) s :
        ↥unitInterval) : ℝ) :=
    vkConvexComb_double_snd hN hk s
  calc ((γ.trans γ').subpath (vkGrid (2 * N) (N + k))
        (vkGrid (2 * N) (N + k + 1))) s
      = (γ.trans γ') (Set.Icc.convexComb (vkGrid (2 * N) (N + k))
        (vkGrid (2 * N) (N + k + 1)) s) := rfl
    _ = γ' (Set.Icc.convexComb (vkGrid N k) (vkGrid N (k + 1)) s) := by
        rw [vkTrans_apply_ge _ _ _ hge]
        congr 1
        exact Subtype.ext hval
    _ = (γ'.subpath (vkGrid N k) (vkGrid N (k + 1))) s := rfl

/-- Admissibility for the concatenated path at the doubled grid: first-half
pieces match `γ`-pieces, second-half pieces match `γ'`-pieces, and tail pieces
are constant at the endpoint. -/
private theorem vkAdm_trans {X : Type*} [TopologicalSpace X] {U V : Set X}
    {x y z : X} (γ : Path x y) (γ' : Path y z)
    (hCover : U ∪ V = Set.univ) {N : ℕ} (hN : 1 ≤ N)
    (hAγ : vkAdm U V γ N) (hAγ' : vkAdm U V γ' N) :
    vkAdm U V (γ.trans γ') (2 * N) := by
  intro k
  by_cases hkN : k < N
  · have hpeq : ∀ s : ↥unitInterval,
        ((γ.trans γ').subpath (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1))) s =
          (γ.subpath (vkGrid N k) (vkGrid N (k + 1))) s :=
        fun s => vkTrans_piece_fst γ γ' hN hkN s
    have hrange : Set.range
        ⇑((γ.trans γ').subpath (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1))) ⊆
        Set.range ⇑(γ.subpath (vkGrid N k) (vkGrid N (k + 1))) := by
      intro w hw
      obtain ⟨s, rfl⟩ := hw
      rw [hpeq s]
      exact ⟨s, rfl⟩
    rcases hAγ k with hU | hV
    · left
      exact hrange.trans hU
    · right
      exact hrange.trans hV
  · push Not at hkN
    by_cases hk2 : k < 2 * N
    · have hj : k - N < N := by omega
      have hkeq : N + (k - N) = k := by omega
      have hpeq : ∀ s : ↥unitInterval,
          ((γ.trans γ').subpath (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1))) s =
            (γ'.subpath (vkGrid N (k - N)) (vkGrid N (k - N + 1))) s := by
        intro s
        have e := vkTrans_piece_snd γ γ' hN hj s
        rw [hkeq] at e
        exact e
      have hrange : Set.range
          ⇑((γ.trans γ').subpath (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1))) ⊆
          Set.range ⇑(γ'.subpath (vkGrid N (k - N)) (vkGrid N (k - N + 1))) := by
        intro w hw
        obtain ⟨s, rfl⟩ := hw
        rw [hpeq s]
        exact ⟨s, rfl⟩
      rcases hAγ' (k - N) with hU | hV
      · left
        exact hrange.trans hU
      · right
        exact hrange.trans hV
    · push Not at hk2
      have htop0 : vkGrid (2 * N) k = 1 := vkGrid_top (by omega) hk2
      have htop1 : vkGrid (2 * N) (k + 1) = 1 := vkGrid_top (by omega) (by omega)
      have htr1 : (γ.trans γ') 1 = z := by
        have h1le : (1 / 2 : ℝ) ≤ ((1 : ↥unitInterval) : ℝ) := by
          have h1c : ((1 : ↥unitInterval) : ℝ) = 1 := rfl
          rw [h1c]
          norm_num
        have e1real : 2 * ((1 : ↥unitInterval) : ℝ) - 1 =
            ((1 : ↥unitInterval) : ℝ) := by
          have h1c : ((1 : ↥unitInterval) : ℝ) = 1 := rfl
          rw [h1c]
          norm_num
        calc (γ.trans γ') 1
            = γ' 1 := by
              rw [vkTrans_apply_ge _ _ _ h1le]
              congr 1
              exact Subtype.ext e1real
          _ = z := γ'.target
      have hconst : ∀ s : ↥unitInterval,
          ((γ.trans γ').subpath (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1))) s =
            z := by
        intro s
        rw [htop0, htop1, Path.subpath_self]
        exact htr1
      have hzr : Set.range
          ⇑((γ.trans γ').subpath (vkGrid (2 * N) k) (vkGrid (2 * N) (k + 1))) ⊆
          {z} := by
        intro w hw
        obtain ⟨s, rfl⟩ := hw
        rw [hconst s]
        exact Set.mem_singleton z
      have hcover : z ∈ U ∪ V := by
        rw [hCover]
        exact Set.mem_univ z
      rcases hcover with hUz | hVz
      · left
        exact hzr.trans (Set.singleton_subset_iff.mpr hUz)
      · right
        exact hzr.trans (Set.singleton_subset_iff.mpr hVz)

/-- `Φ` preserves concatenation. Grid `N1 * N2` is admissible for both
halves; the doubled grid on the concatenation splits into the two halves by
`vkChainSeq_append`, identified via `vkChainSeq_congr`, and the endpoint
`eqToHom`s merge. -/
private theorem vkPhi_trans {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    {x y z : X} (γ : Path x y) (γ' : Path y z) :
    vkPhi F_U F_V hCompat hCover hU hV (γ.trans γ') =
      vkPhi F_U F_V hCompat hCover hU hV γ ≫
        vkPhi F_U F_V hCompat hCover hU hV γ' := by
  obtain ⟨N1, hN1, hA1⟩ := vkLebesgue1D hU hV hCover γ
  obtain ⟨N2, hN2, hA2⟩ := vkLebesgue1D hU hV hCover γ'
  have hN : 1 ≤ N1 * N2 := vkOne_le_mul hN1 hN2
  have hAγ : vkAdm U V γ (N1 * N2) := vkAdm_mul hN1 hN2 hA1
  have hAγ' : vkAdm U V γ' (N1 * N2) := by
    have h := vkAdm_mul hN2 hN1 hA2
    rwa [Nat.mul_comm N2 N1] at h
  have eNN : N1 * N2 + N1 * N2 = 2 * (N1 * N2) := by omega
  have gNN : ∀ k, vkGrid (N1 * N2 + N1 * N2) k = vkGrid (2 * (N1 * N2)) k :=
    fun k => congrArg (fun M => vkGrid M k) eNN
  have hAtrans2 := vkAdm_trans γ γ' hCover hN hAγ hAγ'
  have hNN : 1 ≤ N1 * N2 + N1 * N2 := by omega
  have hAtransNN : vkAdm U V (γ.trans γ') (N1 * N2 + N1 * N2) := by
    rw [eNN]
    exact hAtrans2
  have hPhiT := vkPhi_eq F_U F_V hCompat hCover hU hV (γ.trans γ')
    (N1 * N2 + N1 * N2) hNN hAtransNN
  have hPhiγ := vkPhi_eq F_U F_V hCompat hCover hU hV γ (N1 * N2) hN hAγ
  have hPhiγ' := vkPhi_eq F_U F_V hCompat hCover hU hV γ' (N1 * N2) hN hAγ'
  rw [hPhiT, hPhiγ, hPhiγ']
  have hz1 : ∀ k, k ≤ N1 * N2 →
      (γ.trans γ') (vkGrid (N1 * N2 + N1 * N2) k) = γ (vkGrid (N1 * N2) k) := by
    intro k hk
    rw [gNN k]
    have hle : ((vkGrid (2 * (N1 * N2)) k : ↥unitInterval) : ℝ) ≤ 1 / 2 :=
      vkGrid_le_half hN hk
    have hval : 2 * ((vkGrid (2 * (N1 * N2)) k : ↥unitInterval) : ℝ) =
        ((vkGrid (N1 * N2) k : ↥unitInterval) : ℝ) :=
      vkGrid_double_fst hN hk
    rw [vkTrans_apply_le _ _ _ hle]
    congr 1
    exact Subtype.ext hval
  have hz2 : ∀ k, k ≤ N1 * N2 →
      (γ.trans γ') (vkGrid (N1 * N2 + N1 * N2) (N1 * N2 + k)) =
        γ' (vkGrid (N1 * N2) k) := by
    intro k hk
    rw [gNN (N1 * N2 + k)]
    have hge : (1 / 2 : ℝ) ≤
        ((vkGrid (2 * (N1 * N2)) (N1 * N2 + k) : ↥unitInterval) : ℝ) :=
      vkGrid_half_le hN hk
    have hval : 2 * ((vkGrid (2 * (N1 * N2)) (N1 * N2 + k) :
        ↥unitInterval) : ℝ) - 1 =
        ((vkGrid (N1 * N2) k : ↥unitInterval) : ℝ) :=
      vkGrid_double_snd hN hk
    rw [vkTrans_apply_ge _ _ _ hge]
    congr 1
    exact Subtype.ext hval
  have hm1 : ∀ k, k < N1 * N2 → ∀ s : ↥unitInterval,
      ((γ.trans γ').subpath (vkGrid (N1 * N2 + N1 * N2) k)
        (vkGrid (N1 * N2 + N1 * N2) (k + 1))) s =
        (γ.subpath (vkGrid (N1 * N2) k) (vkGrid (N1 * N2) (k + 1))) s := by
    intro k hk s
    rw [gNN k, gNN (k + 1)]
    exact vkTrans_piece_fst γ γ' hN hk s
  have hm2 : ∀ k, k < N1 * N2 → ∀ s : ↥unitInterval,
      ((γ.trans γ').subpath (vkGrid (N1 * N2 + N1 * N2) (N1 * N2 + k))
        (vkGrid (N1 * N2 + N1 * N2) (N1 * N2 + k + 1))) s =
        (γ'.subpath (vkGrid (N1 * N2) k) (vkGrid (N1 * N2) (k + 1))) s := by
    intro k hk s
    rw [gNN (N1 * N2 + k), gNN (N1 * N2 + k + 1)]
    exact vkTrans_piece_snd γ γ' hN hk s
  have happ := vkChainSeq_append F_U F_V hCompat hCover
    (fun k => (γ.trans γ') (vkGrid (N1 * N2 + N1 * N2) k))
    (fun k => (γ.trans γ').subpath (vkGrid (N1 * N2 + N1 * N2) k)
      (vkGrid (N1 * N2 + N1 * N2) (k + 1)))
    (fun k => hAtransNN k) (N1 * N2) (N1 * N2)
  have hcongr1 := vkChainSeq_congr F_U F_V hCompat hCover
    (fun k => (γ.trans γ') (vkGrid (N1 * N2 + N1 * N2) k))
    (fun k => γ (vkGrid (N1 * N2) k))
    (fun k => (γ.trans γ').subpath (vkGrid (N1 * N2 + N1 * N2) k)
      (vkGrid (N1 * N2 + N1 * N2) (k + 1)))
    (fun k => γ.subpath (vkGrid (N1 * N2) k) (vkGrid (N1 * N2) (k + 1)))
    (fun k => hAtransNN k) (fun k => hAγ k) (N1 * N2) hz1 hm1
  have hcongr2 := vkChainSeq_congr F_U F_V hCompat hCover
    (fun k => (γ.trans γ') (vkGrid (N1 * N2 + N1 * N2) (N1 * N2 + k)))
    (fun k => γ' (vkGrid (N1 * N2) k))
    (fun k => (γ.trans γ').subpath (vkGrid (N1 * N2 + N1 * N2) (N1 * N2 + k))
      (vkGrid (N1 * N2 + N1 * N2) (N1 * N2 + k + 1)))
    (fun k => γ'.subpath (vkGrid (N1 * N2) k) (vkGrid (N1 * N2) (k + 1)))
    (fun k => hAtransNN (N1 * N2 + k)) (fun k => hAγ' k) (N1 * N2) hz2 hm2
  have m0 : eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((congrArg (γ.trans γ') (vkGrid_zero (N1 * N2 + N1 * N2))).trans
          (γ.trans γ').source)).symm ≫
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        (hz1 0 (Nat.zero_le (N1 * N2)))) =
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((congrArg γ (vkGrid_zero (N1 * N2))).trans γ.source)).symm := by
    rw [CategoryTheory.eqToHom_trans]
  have m1 : eqToHom (congrArg (vkObj0 F_U F_V hCover)
        (hz1 (N1 * N2) le_rfl)).symm ≫
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        (hz2 0 (Nat.zero_le (N1 * N2)))) =
      (eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((congrArg γ (vkGrid_top hN le_rfl)).trans γ.target)) ≫
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((congrArg γ' (vkGrid_zero (N1 * N2))).trans γ'.source)).symm) := by
    rw [CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans]
  have m2 : eqToHom (congrArg (vkObj0 F_U F_V hCover)
        (hz2 (N1 * N2) le_rfl)).symm ≫
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((congrArg (γ.trans γ') (vkGrid_top hNN le_rfl)).trans
          (γ.trans γ').target)) =
      eqToHom (congrArg (vkObj0 F_U F_V hCover)
        ((congrArg γ' (vkGrid_top hN le_rfl)).trans γ'.target)) := by
    rw [CategoryTheory.eqToHom_trans]
  unfold vkChain
  rw [happ, hcongr1, hcongr2]
  simp only [Category.assoc]
  rw [m2]
  conv_lhs => rw [← Category.assoc, m0]
  conv_lhs =>
    rhs
    rhs
    rw [← Category.assoc, m1]
  rw [Category.assoc]

/-- The glued functor. -/
private noncomputable def vkF {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V) :
    FundamentalGroupoid X ⥤ G where
  obj x := vkObj0 F_U F_V hCover x.as
  map {x y} q :=
    Quotient.lift (fun p : Path x.as y.as => vkPhi F_U F_V hCompat hCover hU hV p)
      (fun a b h => vkPhi_homotopy_invariant F_U F_V hCompat hCover hU hV h) q
  map_id x := by
    rw [FundamentalGroupoid.id_eq_path_refl]
    change vkPhi F_U F_V hCompat hCover hU hV (Path.refl x.as) = 𝟙 _
    exact vkPhi_refl F_U F_V hCompat hCover hU hV x.as
  map_comp f g := by
    induction f using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction g using Path.Homotopic.Quotient.ind with
      | mk q =>
        rw [FundamentalGroupoid.comp_eq, ← Path.Homotopic.Quotient.mk_trans]
        change vkPhi F_U F_V hCompat hCover hU hV (p.trans q) =
          vkPhi F_U F_V hCompat hCover hU hV p ≫
            vkPhi F_U F_V hCompat hCover hU hV q
        exact vkPhi_trans F_U F_V hCompat hCover hU hV p q

/-- The composite functor sends a path class to `Φ` of the mapped path. -/
private theorem vkF_comp_map_mk {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    {W : Set X} {x y : FundamentalGroupoid ↥W} (p : Path x.as y.as) :
    (FundamentalGroupoid.map (inclusionSub (X := X) W) ⋙
      vkF F_U F_V hCompat hCover hU hV).map
      (Path.Homotopic.Quotient.mk p) =
    vkPhi F_U F_V hCompat hCover hU hV
      (p.map (inclusionSub (X := X) W).continuous) := rfl

/-- First triangle equation. -/
private theorem vkF_spec_U {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V) :
    FundamentalGroupoid.map (inclusionSub (X := X) U) ⋙
      vkF F_U F_V hCompat hCover hU hV = F_U := by
  have hobj : ∀ Z : FundamentalGroupoid ↥U,
      (FundamentalGroupoid.map (inclusionSub (X := X) U) ⋙
        vkF F_U F_V hCompat hCover hU hV).obj Z = F_U.obj Z := by
    rintro ⟨⟨x, hx⟩⟩
    exact vkObj0_eq_U F_U F_V hCover hx
  refine CategoryTheory.Functor.ext hobj ?_
  · intro x y f
    induction f using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [vkF_comp_map_mk]
      have hU' : Set.range ⇑(p.map (inclusionSub (X := X) U).continuous) ⊆
          U := by
        intro w hw
        obtain ⟨t, rfl⟩ := hw
        exact (p t).2
      have hs : vkSmall U V (p.map (inclusionSub (X := X) U).continuous) :=
        Or.inl hU'
      rw [vkPhi_small F_U F_V hCompat hCover hU hV _ hs,
        vkLoc_of_mem_U F_U F_V hCompat hCover _ _ hU']
      unfold vkLU
      have hq : vkRes U (p.map (inclusionSub (X := X) U).continuous) hU' =
          p := by
        apply Path.ext
        rfl
      rw [hq]
      congr 1

/-- Second triangle equation. -/
private theorem vkF_spec_V {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V) :
    FundamentalGroupoid.map (inclusionSub (X := X) V) ⋙
      vkF F_U F_V hCompat hCover hU hV = F_V := by
  have hobj : ∀ Z : FundamentalGroupoid ↥V,
      (FundamentalGroupoid.map (inclusionSub (X := X) V) ⋙
        vkF F_U F_V hCompat hCover hU hV).obj Z = F_V.obj Z := by
    rintro ⟨⟨x, hx⟩⟩
    exact vkObj0_eq_V F_U F_V hCompat hCover hx
  refine CategoryTheory.Functor.ext hobj ?_
  · intro x y f
    induction f using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [vkF_comp_map_mk]
      have hV' : Set.range ⇑(p.map (inclusionSub (X := X) V).continuous) ⊆
          V := by
        intro w hw
        obtain ⟨t, rfl⟩ := hw
        exact (p t).2
      have hs : vkSmall U V (p.map (inclusionSub (X := X) V).continuous) :=
        Or.inr hV'
      rw [vkPhi_small F_U F_V hCompat hCover hU hV _ hs,
        vkLoc_eq_lV F_U F_V hCompat hCover hs hV']
      unfold vkLV
      have hq : vkRes V (p.map (inclusionSub (X := X) V).continuous) hV' =
          p := by
        apply Path.ext
        rfl
      rw [hq]
      congr 1

/-- Any functor out of `π(X)` sends `eqToHom` to `eqToHom`. -/
private theorem vkFunctor_map_eqToHom {X : Type*} [TopologicalSpace X]
    {G : Type*} [Groupoid G] (F : FundamentalGroupoid X ⥤ G)
    {a b : FundamentalGroupoid X} (h : a = b) :
    F.map (eqToHom h) = eqToHom (congrArg F.obj h) := by
  cases h
  simp

/-- Any functor out of `π(X)` sends a cast class to the conjugated value. -/
private theorem vkFunctor_map_cast {X : Type*} [TopologicalSpace X]
    {G : Type*} [Groupoid G] (F : FundamentalGroupoid X ⥤ G)
    {x y x' y' : X} (q : Path.Homotopic.Quotient x y) (hx : x' = x)
    (hy : y' = y) :
    F.map (q.cast hx hy) = eqToHom
        (congrArg F.obj (congrArg FundamentalGroupoid.mk hx)) ≫
      F.map q ≫ eqToHom
        (congrArg F.obj (congrArg FundamentalGroupoid.mk hy)).symm := by
  have hcast := (FundamentalGroupoid.conj_eqToHom (p := q) hx hy).symm
  rw [hcast, Functor.map_comp, Functor.map_comp,
    vkFunctor_map_eqToHom F _, vkFunctor_map_eqToHom F _]

/-- Grid induction for uniqueness: `F'` on a long subpath equals the conjugated
grid chain. The step splits the subpath with `mk_subpath_trans_mk_subpath` and
merges the middle `eqToHom`s. -/
private theorem vkUnique_chain {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ)
    (F' : FundamentalGroupoid X ⥤ G)
    (hobj : ∀ w : X, F'.obj (FundamentalGroupoid.mk w) =
      vkObj0 F_U F_V hCover w)
    (hsmall : ∀ {a b : X} (p : Path a b) (hs : vkSmall U V p),
      F'.map (Path.Homotopic.Quotient.mk p) =
      eqToHom (hobj a) ≫ vkLoc F_U F_V hCompat hCover p hs ≫
        eqToHom (hobj b).symm)
    {a b : X} (γ : Path a b) (N : ℕ) (hA : vkAdm U V γ N) (m : ℕ) :
    F'.map (Path.Homotopic.Quotient.mk
        (γ.subpath (vkGrid N 0) (vkGrid N m))) =
      eqToHom (hobj (γ (vkGrid N 0))) ≫
        vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
          (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
          (fun k => hA k) m ≫
        eqToHom (hobj (γ (vkGrid N m))).symm := by
  induction m with
  | zero =>
    have e0 : γ.subpath (vkGrid N 0) (vkGrid N 0) =
        Path.refl (γ (vkGrid N 0)) := Path.subpath_self _ _
    have hmap : F'.map
        (Path.Homotopic.Quotient.mk (Path.refl (γ (vkGrid N 0)))) =
        𝟙 _ := CategoryTheory.Functor.map_id _ _
    have hR : eqToHom (hobj (γ (vkGrid N 0))) ≫
        𝟙 (vkObj0 F_U F_V hCover (γ (vkGrid N 0))) ≫
        eqToHom (hobj (γ (vkGrid N 0))).symm = 𝟙 _ :=
      calc eqToHom (hobj (γ (vkGrid N 0))) ≫
              𝟙 (vkObj0 F_U F_V hCover (γ (vkGrid N 0))) ≫
              eqToHom (hobj (γ (vkGrid N 0))).symm
          = eqToHom (hobj (γ (vkGrid N 0))) ≫
              eqToHom (hobj (γ (vkGrid N 0))).symm :=
            congrArg (eqToHom (hobj (γ (vkGrid N 0))) ≫ ·)
              (Category.id_comp
                (eqToHom (hobj (γ (vkGrid N 0))).symm))
        _ = 𝟙 _ := vkEqToHom_fwd (hobj (γ (vkGrid N 0)))
          (hobj (γ (vkGrid N 0)))
    rw [e0, hmap]
    exact hR.symm
  | succ m ihm =>
    have eSplit := (Path.Homotopic.mk_subpath_trans_mk_subpath γ
      (vkGrid N 0) (vkGrid N m) (vkGrid N (m + 1))).symm
    have hsm := hsmall (γ.subpath (vkGrid N m) (vkGrid N (m + 1))) (hA m)
    have hmid : eqToHom (hobj (γ (vkGrid N m))).symm ≫
        eqToHom (hobj (γ (vkGrid N m))) = 𝟙 _ :=
      vkEqToHom_mid (hobj (γ (vkGrid N m))) (hobj (γ (vkGrid N m)))
    rw [eSplit, ← FundamentalGroupoid.comp_eq, Functor.map_comp, ihm, hsm,
      vkChainSeq_succ]
    exact vkComp_mid _ _ _ _ _ _ hmid

/-- The full-grid subpath is the cast of the path. -/
private theorem vkUnique_subpath_cast {X : Type*} [TopologicalSpace X]
    {a b : X} (γ : Path a b) (N : ℕ) (hN : 1 ≤ N)
    (ha : γ (vkGrid N 0) = a) (hb : γ (vkGrid N N) = b) :
    γ.subpath (vkGrid N 0) (vkGrid N N) = γ.cast ha hb := by
  apply Path.ext
  funext s
  have h1 : (γ.subpath (vkGrid N 0) (vkGrid N N)) s =
      γ (Set.Icc.convexComb (vkGrid N 0) (vkGrid N N) s) := rfl
  have h2 : (γ.cast ha hb) s = γ s := rfl
  rw [h1, h2]
  congr 1
  rw [vkGrid_zero, vkGrid_top hN le_rfl]
  exact Set.Icc.convexComb_zero_one s

/-- Per-path characterization for uniqueness: `F'` on any path class equals the
conjugated `Φ` value. -/
private theorem vkUnique_map {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    (F' : FundamentalGroupoid X ⥤ G)
    (hobj : ∀ w : X, F'.obj (FundamentalGroupoid.mk w) =
      vkObj0 F_U F_V hCover w)
    (hsmall : ∀ {a b : X} (p : Path a b) (hs : vkSmall U V p),
      F'.map (Path.Homotopic.Quotient.mk p) =
      eqToHom (hobj a) ≫ vkLoc F_U F_V hCompat hCover p hs ≫
        eqToHom (hobj b).symm)
    {a b : X} (γ : Path a b) :
    F'.map (Path.Homotopic.Quotient.mk γ) =
      eqToHom (hobj a) ≫ vkPhi F_U F_V hCompat hCover hU hV γ ≫
        eqToHom (hobj b).symm := by
  obtain ⟨N, hN, hA⟩ := vkLebesgue1D hU hV hCover γ
  have hQ := vkUnique_chain F_U F_V hCompat hCover F' hobj hsmall γ N hA N
  have ha : γ (vkGrid N 0) = a := (congrArg γ (vkGrid_zero N)).trans γ.source
  have hb : γ (vkGrid N N) = b :=
    (congrArg γ (vkGrid_top hN le_rfl)).trans γ.target
  have eSub := vkUnique_subpath_cast γ N hN ha hb
  rw [eSub, Path.Homotopic.Quotient.mk_cast, vkFunctor_map_cast] at hQ
  rw [vkPhi_eq F_U F_V hCompat hCover hU hV γ N hN hA]
  unfold vkChain
  have step1 : F'.map (Path.Homotopic.Quotient.mk γ) ≫
      eqToHom (congrArg F'.obj
        (congrArg FundamentalGroupoid.mk hb)).symm =
      eqToHom (congrArg F'.obj
        (congrArg FundamentalGroupoid.mk ha)).symm ≫
      (eqToHom (hobj (γ (vkGrid N 0))) ≫
        vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
          (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
          (fun k => hA k) N ≫
        eqToHom (hobj (γ (vkGrid N N))).symm) :=
    (CategoryTheory.eqToHom_comp_iff
      (congrArg F'.obj (congrArg FundamentalGroupoid.mk ha)) _ _).mp hQ
  have hQx : F'.map (Path.Homotopic.Quotient.mk γ) =
      (eqToHom (congrArg F'.obj
        (congrArg FundamentalGroupoid.mk ha)).symm ≫
        (eqToHom (hobj (γ (vkGrid N 0))) ≫
          vkChainSeq F_U F_V hCompat hCover (fun k => γ (vkGrid N k))
            (fun k => γ.subpath (vkGrid N k) (vkGrid N (k + 1)))
            (fun k => hA k) N ≫
          eqToHom (hobj (γ (vkGrid N N))).symm)) ≫
      eqToHom (congrArg F'.obj
        (congrArg FundamentalGroupoid.mk hb)).symm.symm :=
    (CategoryTheory.comp_eqToHom_iff
      (congrArg F'.obj (congrArg FundamentalGroupoid.mk hb)).symm _ _).mp
      step1
  rw [hQx]
  simp only [Category.assoc, CategoryTheory.eqToHom_trans]
  simp only [← Category.assoc, CategoryTheory.eqToHom_trans]

/-- Uniqueness. -/
private theorem vkUnique {X : Type*} [TopologicalSpace X] {U V : Set X}
    {G : Type*} [Groupoid G] (F_U : FundamentalGroupoid ↥U ⥤ G)
    (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
      (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V)
    (hCover : U ∪ V = Set.univ) (hU : IsOpen U) (hV : IsOpen V)
    (F' : FundamentalGroupoid X ⥤ G)
    (hU' : FundamentalGroupoid.map (inclusionSub (X := X) U) ⋙ F' = F_U)
    (hV' : FundamentalGroupoid.map (inclusionSub (X := X) V) ⋙ F' = F_V) :
    F' = vkF F_U F_V hCompat hCover hU hV := by
  have hobj : ∀ w : X, F'.obj (FundamentalGroupoid.mk w) =
      vkObj0 F_U F_V hCover w := by
    intro w
    have hxU : w ∈ U ∪ V := by
      rw [hCover]
      exact Set.mem_univ w
    rcases hxU with hUx | hVx
    · have h := Functor.congr_obj hU'
        (FundamentalGroupoid.mk (⟨w, hUx⟩ : ↥U))
      rw [vkObj0_eq_U F_U F_V hCover hUx]
      exact h
    · have h := Functor.congr_obj hV'
        (FundamentalGroupoid.mk (⟨w, hVx⟩ : ↥V))
      rw [vkObj0_eq_V F_U F_V hCompat hCover hVx]
      exact h
  have hsmall : ∀ {a b : X} (p : Path a b) (hs : vkSmall U V p),
      F'.map (Path.Homotopic.Quotient.mk p) =
      eqToHom (hobj a) ≫ vkLoc F_U F_V hCompat hCover p hs ≫
        eqToHom (hobj b).symm := by
    intro a b p hs
    have hc := hs
    rcases hc with hUp | hVp
    · have hcU := Functor.congr_hom hU'
        (Path.Homotopic.Quotient.mk (vkRes U p hUp))
      have epath : (vkRes U p hUp).map
          (inclusionSub (X := X) U).continuous = p := by
        apply Path.ext
        rfl
      have qmap : ((FundamentalGroupoid.map (inclusionSub (X := X) U)).map
          (Path.Homotopic.Quotient.mk (vkRes U p hUp))) =
          Path.Homotopic.Quotient.mk p := by
        have hmk : Path.Homotopic.Quotient.mk
            ((vkRes U p hUp).map (inclusionSub (X := X) U).continuous) =
            Path.Homotopic.Quotient.mk p := congrArg _ epath
        rwa [Path.Homotopic.Quotient.mk_map] at hmk
      have eL : F'.map (Path.Homotopic.Quotient.mk p) =
          ((FundamentalGroupoid.map (inclusionSub (X := X) U)) ⋙ F').map
            (Path.Homotopic.Quotient.mk (vkRes U p hUp)) := by
        rw [← qmap]
        rfl
      rw [vkLoc_of_mem_U F_U F_V hCompat hCover p hs hUp]
      unfold vkLU
      rw [eL, hcU]
      simp only [Category.assoc]
      have mL : eqToHom (hobj a) ≫
          eqToHom (vkObj0_eq_U F_U F_V hCover
            (vkMem_of_subset hUp ⟨0, p.source⟩)) =
          eqToHom (Functor.congr_obj hU'
            (FundamentalGroupoid.mk (⟨a, hUp ⟨0, p.source⟩⟩ : ↥U))) := by
        rw [CategoryTheory.eqToHom_trans]; exact vkEqToHom_eq _ _
      have mR : eqToHom (vkObj0_eq_U F_U F_V hCover
            (vkMem_of_subset hUp ⟨1, p.target⟩)).symm ≫
          eqToHom (hobj b).symm =
          eqToHom (Functor.congr_obj hU'
            (FundamentalGroupoid.mk (⟨b, hUp ⟨1, p.target⟩⟩ : ↥U))).symm := by
        rw [CategoryTheory.eqToHom_trans]; exact vkEqToHom_eq _ _
      conv_rhs => rw [← Category.assoc, mL]
      conv_rhs =>
        rhs
        rhs
        rw [mR]
      congr 1
    · have hcV := Functor.congr_hom hV'
        (Path.Homotopic.Quotient.mk (vkRes V p hVp))
      have epath : (vkRes V p hVp).map
          (inclusionSub (X := X) V).continuous = p := by
        apply Path.ext
        rfl
      have qmap : ((FundamentalGroupoid.map (inclusionSub (X := X) V)).map
          (Path.Homotopic.Quotient.mk (vkRes V p hVp))) =
          Path.Homotopic.Quotient.mk p := by
        have hmk : Path.Homotopic.Quotient.mk
            ((vkRes V p hVp).map (inclusionSub (X := X) V).continuous) =
            Path.Homotopic.Quotient.mk p := congrArg _ epath
        rwa [Path.Homotopic.Quotient.mk_map] at hmk
      have eL : F'.map (Path.Homotopic.Quotient.mk p) =
          ((FundamentalGroupoid.map (inclusionSub (X := X) V)) ⋙ F').map
            (Path.Homotopic.Quotient.mk (vkRes V p hVp)) := by
        rw [← qmap]
        rfl
      rw [vkLoc_eq_lV F_U F_V hCompat hCover hs hVp]
      unfold vkLV
      rw [eL, hcV]
      simp only [Category.assoc]
      have mL : eqToHom (hobj a) ≫
          eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
            (vkMem_of_subset hVp ⟨0, p.source⟩)) =
          eqToHom (Functor.congr_obj hV'
            (FundamentalGroupoid.mk (⟨a, hVp ⟨0, p.source⟩⟩ : ↥V))) := by
        rw [CategoryTheory.eqToHom_trans]; exact vkEqToHom_eq _ _
      have mR : eqToHom (vkObj0_eq_V F_U F_V hCompat hCover
            (vkMem_of_subset hVp ⟨1, p.target⟩)).symm ≫
          eqToHom (hobj b).symm =
          eqToHom (Functor.congr_obj hV'
            (FundamentalGroupoid.mk (⟨b, hVp ⟨1, p.target⟩⟩ : ↥V))).symm := by
        rw [CategoryTheory.eqToHom_trans]; exact vkEqToHom_eq _ _
      conv_rhs => rw [← Category.assoc, mL]
      conv_rhs =>
        rhs
        rhs
        rw [mR]
      congr 1
  have hmap : ∀ {a b : X} (γ : Path a b),
      F'.map (Path.Homotopic.Quotient.mk γ) =
        eqToHom (hobj a) ≫
          (vkF F_U F_V hCompat hCover hU hV).map
            (Path.Homotopic.Quotient.mk γ) ≫
          eqToHom (hobj b).symm := by
    intro a b γ
    have hFmap : (vkF F_U F_V hCompat hCover hU hV).map
        (Path.Homotopic.Quotient.mk γ) =
        vkPhi F_U F_V hCompat hCover hU hV γ := rfl
    rw [hFmap]
    exact vkUnique_map F_U F_V hCompat hCover hU hV F' hobj hsmall γ
  have hobj' : ∀ Z : FundamentalGroupoid X,
      F'.obj Z = (vkF F_U F_V hCompat hCover hU hV).obj Z := by
    rintro ⟨w⟩
    exact hobj w
  refine CategoryTheory.Functor.ext hobj' ?_
  intro x y f
  induction f using Path.Homotopic.Quotient.ind with
  | mk p => exact hmap p


/--
For open `U, V` covering `X`, compatible functors from `π(U)`, `π(V)` that agree on `π(U ∩ V)`
extend uniquely to `π(X)`, and the canonical square of inclusion-induced functors commutes.
Source: H. Seifert 1931 and E. van Kampen 1933; groupoid form Brown, Topology and Groupoids Chap
6; Hatcher, Algebraic Topology; nLab Seifert–van Kampen theorem. Lean fundamental-groupoid
universal-property pushout form.

Proves `Wanted` entry `seifert_vanKampen_fundamentalGroupoid_universalProperty`.
-/
public theorem seifert_vanKampen_fundamentalGroupoid_universalProperty
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    {G : Type*} [Groupoid G]
    (F_U : FundamentalGroupoid ↥U ⥤ G) (F_V : FundamentalGroupoid ↥V ⥤ G)
    (hCompat : (FundamentalGroupoid.map (inclusionInterLeft U V)) ⋙ F_U =
               (FundamentalGroupoid.map (inclusionInterRight U V)) ⋙ F_V) :
    (FundamentalGroupoid.map (inclusionInterLeft U V) ⋙
        FundamentalGroupoid.map (inclusionSub (X := X) U) =
      FundamentalGroupoid.map (inclusionInterRight U V) ⋙
        FundamentalGroupoid.map (inclusionSub (X := X) V)) ∧
    ∃! (F : FundamentalGroupoid X ⥤ G),
      (FundamentalGroupoid.map (inclusionSub (X := X) U)) ⋙ F = F_U ∧
      (FundamentalGroupoid.map (inclusionSub (X := X) V)) ⋙ F = F_V := by
  refine ⟨vk_square_comm, ?_⟩
  refine ExistsUnique.intro (vkF F_U F_V hCompat hCover hU hV)
    ⟨vkF_spec_U F_U F_V hCompat hCover hU hV,
     vkF_spec_V F_U F_V hCompat hCover hU hV⟩ ?_
  intro F' hF'
  obtain ⟨hU', hV'⟩ := hF'
  exact vkUnique F_U F_V hCompat hCover hU hV F' hU' hV'

end MathlibExt.Topology.Homotopy.VanKampenWanted
