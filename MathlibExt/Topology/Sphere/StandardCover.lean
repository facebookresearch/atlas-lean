/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Instances.SphereStereographic
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Standard covers of spheres
-/

@[expose] public section

open CategoryTheory
open Metric

namespace AlgebraicTopology

universe v u

lemma contractibleSpace_sphere_compl_singleton (n : ℕ) {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = n + 1)] (v : Metric.sphere (0 : E) 1) :
    ContractibleSpace ↥(({v}ᶜ : Set (Metric.sphere (0 : E) 1))) := by
  set e := stereographic' n v with he
  have hsrc : e.source = {v}ᶜ := stereographic'_source v
  let φ : ↥({v}ᶜ : Set (Metric.sphere (0:E) 1)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    { toFun := fun x => e x.1
      invFun := fun y => ⟨e.symm y, by
        have : e.symm y ∈ e.source := by
          apply e.map_target
          rw [stereographic'_target]
          trivial
        rw [hsrc] at this
        exact this⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        simp only
        rw [e.left_inv]
        rw [hsrc]
        exact hx
      right_inv := by
        intro y
        simp only
        rw [e.right_inv]
        rw [stereographic'_target]
        trivial
      continuous_toFun := by
        apply e.continuousOn_toFun.comp_continuous continuous_subtype_val
        intro x
        rw [hsrc]
        exact x.2
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply e.continuousOn_invFun.comp_continuous continuous_id
        intro y
        rw [stereographic'_target]
        trivial }
  exact φ.contractibleSpace

def uliftComplHomeomorph {α : Type v} [TopologicalSpace α] (w : α) :
    ↥(({ULift.up.{u, v} w}ᶜ : Set (ULift.{u, v} α))) ≃ₜ ↥(({w}ᶜ : Set α)) where
  toFun := fun x => ⟨x.1.down, fun h => x.2 (ULift.down_injective h)⟩
  invFun := fun y => ⟨ULift.up y.1, fun h => y.2 (congrArg ULift.down h)⟩
  left_inv := fun x => by apply Subtype.ext; rfl
  right_inv := fun y => by apply Subtype.ext; rfl
  continuous_toFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _

def uliftComplTwoHomeomorph {α : Type v} [TopologicalSpace α] (a b : α) :
    ↥(({ULift.up.{u, v} a, ULift.up.{u, v} b}ᶜ : Set (ULift.{u, v} α))) ≃ₜ
      ↥(({a, b}ᶜ : Set α)) where
  toFun := fun x => ⟨x.1.down, by
    rcases x with ⟨⟨xd⟩, hx⟩
    simp only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢
    exact fun h => hx (h.imp (fun e => by rw [e]) (fun e => by rw [e]))⟩
  invFun := fun y => ⟨ULift.up y.1, by
    rcases y with ⟨yd, hy⟩
    simp only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, ULift.up.injEq] at hy ⊢
    exact hy⟩
  left_inv := fun x => by apply Subtype.ext; rfl
  right_inv := fun y => by apply Subtype.ext; rfl
  continuous_toFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _

noncomputable def northPt (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩

noncomputable def southPt (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single (Fin.last n) (-1), by simp⟩

noncomputable def sphereCoverA (n : ℕ) : Set ↥(TopCat.sphere.{u} n) :=
  (Set.singleton (ULift.up.{u, 0} (southPt n))).compl
noncomputable def sphereCoverB (n : ℕ) : Set ↥(TopCat.sphere.{u} n) :=
  (Set.singleton (ULift.up.{u, 0} (northPt n))).compl

lemma isOpen_sphereCoverA (n : ℕ) : IsOpen (sphereCoverA.{u} n) := by
  have : T1Space ↥(TopCat.sphere.{u} n) := by
    change T1Space (ULift ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    infer_instance
  exact isOpen_compl_singleton

lemma isOpen_sphereCoverB (n : ℕ) : IsOpen (sphereCoverB.{u} n) := by
  have : T1Space ↥(TopCat.sphere.{u} n) := by
    change T1Space (ULift ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    infer_instance
  exact isOpen_compl_singleton

lemma northPt_ne_southPt (n : ℕ) : northPt n ≠ southPt n := by
  intro h
  have hc : (northPt n : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) =
      (southPt n : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) := by rw [h]
  simp only [northPt, southPt, PiLp.single_apply] at hc
  norm_num at hc

lemma sphereCover_union (n : ℕ) :
    sphereCoverA.{u} n ∪ sphereCoverB.{u} n = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  show x ∈ sphereCoverA.{u} n ∨ x ∈ sphereCoverB.{u} n
  simp only [sphereCoverA, sphereCoverB]
  have hne :
      (ULift.up.{u, 0} (southPt n) : ↥(TopCat.sphere.{u} n)) ≠
        ULift.up.{u, 0} (northPt n) := by
    intro heq
    have h' := congrArg ULift.down heq
    exact northPt_ne_southPt n h'.symm
  by_cases hx : x = ULift.up.{u, 0} (southPt n)
  · right
    intro heq
    have : ULift.up.{u, 0} (southPt n) =
        (ULift.up.{u, 0} (northPt n) : ↥(TopCat.sphere.{u} n)) :=
      hx.symm.trans heq
    exact hne this
  · left
    exact hx

lemma sphereCover_interiorsCover (n : ℕ) :
    (Set.univ : Set ↥(TopCat.sphere.{u} n)) ⊆
      interior (sphereCoverA.{u} n) ∪ interior (sphereCoverB.{u} n) := by
  have hA : interior (sphereCoverA.{u} n) = sphereCoverA.{u} n :=
    (isOpen_sphereCoverA.{u} n).interior_eq
  have hB : interior (sphereCoverB.{u} n) = sphereCoverB.{u} n :=
    (isOpen_sphereCoverB.{u} n).interior_eq
  rw [hA, hB, sphereCover_union.{u} n]

instance contractibleSpace_sphereCoverA (n : ℕ) :
    ContractibleSpace ↥(sphereCoverA.{u} n) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  have := contractibleSpace_sphere_compl_singleton n (southPt n)
  have h : ContractibleSpace
      ↥(({ULift.up.{u, 0} (southPt n)}ᶜ :
        Set (ULift.{u, 0} ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))) :=
    (uliftComplHomeomorph.{0, u} (southPt n)).contractibleSpace
  exact h

instance contractibleSpace_sphereCoverB (n : ℕ) :
    ContractibleSpace ↥(sphereCoverB.{u} n) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  have := contractibleSpace_sphere_compl_singleton n (northPt n)
  have h : ContractibleSpace
      ↥(({ULift.up.{u, 0} (northPt n)}ᶜ :
        Set (ULift.{u, 0} ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))) :=
    (uliftComplHomeomorph.{0, u} (northPt n)).contractibleSpace
  exact h

lemma sphereCover_inter (n : ℕ) :
    sphereCoverA.{u} n ∩ sphereCoverB.{u} n =
      ({ULift.up.{u, 0} (southPt n), ULift.up.{u, 0} (northPt n)}ᶜ :
        Set ↥(TopCat.sphere.{u} n)) := by
  ext x
  simp only [sphereCoverA, sphereCoverB]
  constructor
  · rintro ⟨h1, h2⟩
    intro h
    rcases h with h | h
    · exact h1 h
    · exact h2 h
  · intro h
    constructor
    · intro heq
      exact h (Or.inl heq)
    · intro heq
      exact h (Or.inr heq)

lemma northPt_eq_neg_southPt (n : ℕ) :
    (northPt n : EuclideanSpace ℝ (Fin (n+1))) = -(southPt n) := by
  rw [northPt, southPt]
  ext i
  simp only [PiLp.single_apply, PiLp.neg_apply]
  split_ifs <;> norm_num

noncomputable def ioiProj (Y : TopCat.{u}) :
    TopCat.of (Y × ↥(Set.Ioi (0:ℝ))) ⟶ Y :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

noncomputable def ioiSect (Y : TopCat.{u}) :
    Y ⟶ TopCat.of (Y × ↥(Set.Ioi (0:ℝ))) :=
  TopCat.ofHom ⟨fun y => (y, ⟨1, by norm_num⟩), by fun_prop⟩

lemma ioiSect_comp_ioiProj (Y : TopCat.{u}) :
    ioiSect Y ≫ ioiProj Y = 𝟙 Y := by
  apply TopCat.hom_ext; ext y; rfl

noncomputable def ioiContraction (Y : TopCat.{u}) :
    TopCat.Homotopy (ioiProj Y ≫ ioiSect Y)
      (𝟙 (TopCat.of (Y × ↥(Set.Ioi (0:ℝ))))) where
  toFun := fun p => (p.2.1, ⟨(1 - (p.1:ℝ)) * 1 + (p.1:ℝ) * p.2.2.1, by
    have h1 : (0:ℝ) ≤ 1 - (p.1:ℝ) := by have := p.1.2.2; linarith
    have h2 : (0:ℝ) ≤ (p.1:ℝ) := p.1.2.1
    rcases eq_or_lt_of_le h2 with h | h
    · simp [← h]
    · have := p.2.2.2; simp only [Set.mem_Ioi] at this ⊢; positivity⟩)
  continuous_toFun := by fun_prop
  map_zero_left := fun p => by apply Prod.ext <;> simp [ioiProj, ioiSect]
  map_one_left := fun p => by apply Prod.ext <;> simp

noncomputable def equatorHomeo (m : ℕ) :
    ↥(sphereCoverA.{u} (m + 1) ∩ sphereCoverB.{u} (m + 1)) ≃ₜ
      (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ×
        ↥(Set.Ioi (0:ℝ))) := by
  have : Fact
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1 + 1))) = m + 1 + 1) :=
    ⟨by simp⟩
  exact (Homeomorph.setCongr (sphereCover_inter.{u} (m + 1))).trans
    ((uliftComplTwoHomeomorph.{0, u} (southPt (m + 1)) (northPt (m + 1))).trans
      ((spherePuncturedTwoHomeo (m + 1) (southPt (m + 1)) (northPt (m + 1))
          (northPt_eq_neg_southPt (m + 1))).trans
        (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (m + 1))))))

/-- Positive-dimensional spheres are path-connected, universe-polymorphic. -/
lemma pathConnectedSpace_sphere (n : ℕ) (hn : n ≠ 0) :
    PathConnectedSpace ↥(TopCat.sphere.{u} n) := by
  have hlt : (1 : ℕ) < n + 1 := by
    cases n with
    | zero => exact absurd rfl hn
    | succ m => exact Nat.succ_lt_succ (Nat.zero_lt_succ m)
  have hrank :
      (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hlt
  have his :
      IsPathConnected
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) (1 : ℝ)) :=
    isPathConnected_sphere hrank 0 (by norm_num)
  have : PathConnectedSpace
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp his
  exact
    (show Function.Surjective
        (ULift.up :
          ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
            ULift.{u} _) from
      fun y => ⟨y.down, rfl⟩).pathConnectedSpace
      continuous_uliftUp

instance (n : ℕ) [NeZero n] : PathConnectedSpace ↥(TopCat.sphere.{u} n) :=
  pathConnectedSpace_sphere n (NeZero.ne n)

/-! ### Antipodal -/

noncomputable def sphereAntipodalHomeo (n : ℕ) :
    ↥(TopCat.sphere.{u} n) ≃ₜ ↥(TopCat.sphere.{u} n) :=
  let E := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  (Homeomorph.ulift.{u, 0} (X := E)).trans (Homeomorph.neg E) |>.trans
    (Homeomorph.ulift.{u, 0} (X := E)).symm

lemma sphereAntipodalHomeo_apply (n : ℕ) (x : ↥(TopCat.sphere.{u} n)) :
    sphereAntipodalHomeo n x = ULift.up (-x.down) :=
  rfl

@[simp]
lemma sphereAntipodalHomeo_apply_apply (n : ℕ) (x : ↥(TopCat.sphere.{u} n)) :
    sphereAntipodalHomeo n (sphereAntipodalHomeo n x) = x := by
  change ULift.up (- -x.down) = x
  rw [neg_neg]
  cases x
  rfl

lemma sphereAntipodalHomeo_involutive (n : ℕ) :
    Function.Involutive (sphereAntipodalHomeo n) :=
  fun x => sphereAntipodalHomeo_apply_apply n x

noncomputable def sphereAntipodalMap (n : ℕ) :
    TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n :=
  (TopCat.isoOfHomeo (sphereAntipodalHomeo n)).hom

lemma sphereAntipodalMap_apply (n : ℕ) (x : ↥(TopCat.sphere.{u} n)) :
    (sphereAntipodalMap n) x = ULift.up (-x.down) :=
  rfl

@[simp]
lemma sphereAntipodalMap_comp_self (n : ℕ) :
    sphereAntipodalMap n ≫ sphereAntipodalMap n = 𝟙 (TopCat.sphere.{u} n) := by
  apply TopCat.hom_ext
  ext x
  have : (sphereAntipodalMap n ≫ sphereAntipodalMap n) x =
      sphereAntipodalHomeo n (sphereAntipodalHomeo n x) := rfl
  rw [this, sphereAntipodalHomeo_apply_apply]
  rfl

@[simp]
lemma sphereAntipodalHomeo_northPt (n : ℕ) :
    sphereAntipodalHomeo n (ULift.up.{u, 0} (northPt n)) =
      ULift.up.{u, 0} (southPt n) := by
  change (ULift.up.{u, 0} (-(northPt n)) : ↥(TopCat.sphere.{u} n)) =
      ULift.up.{u, 0} (southPt n)
  rw [ULift.up.injEq]
  apply Subtype.ext
  change -((northPt n : EuclideanSpace ℝ (Fin (n + 1)))) =
      (southPt n : EuclideanSpace ℝ (Fin (n + 1)))
  rw [northPt_eq_neg_southPt (n := n), neg_neg]

@[simp]
lemma sphereAntipodalHomeo_southPt (n : ℕ) :
    sphereAntipodalHomeo n (ULift.up.{u, 0} (southPt n)) =
      ULift.up.{u, 0} (northPt n) := by
  change (ULift.up.{u, 0} (-(southPt n)) : ↥(TopCat.sphere.{u} n)) =
      ULift.up.{u, 0} (northPt n)
  rw [ULift.up.injEq]
  apply Subtype.ext
  change -((southPt n : EuclideanSpace ℝ (Fin (n + 1)))) =
      (northPt n : EuclideanSpace ℝ (Fin (n + 1)))
  rw [← northPt_eq_neg_southPt (n := n)]

@[simp]
lemma sphereAntipodalMap_northPt (n : ℕ) :
    (sphereAntipodalMap n) (ULift.up.{u, 0} (northPt n)) =
      ULift.up.{u, 0} (southPt n) := by
  rw [show (sphereAntipodalMap n) (ULift.up.{u, 0} (northPt n)) =
      sphereAntipodalHomeo n (ULift.up.{u, 0} (northPt n)) from rfl,
      sphereAntipodalHomeo_northPt]

@[simp]
lemma sphereAntipodalMap_southPt (n : ℕ) :
    (sphereAntipodalMap n) (ULift.up.{u, 0} (southPt n)) =
      ULift.up.{u, 0} (northPt n) := by
  rw [show (sphereAntipodalMap n) (ULift.up.{u, 0} (southPt n)) =
      sphereAntipodalHomeo n (ULift.up.{u, 0} (southPt n)) from rfl,
      sphereAntipodalHomeo_southPt]

section S0

lemma sphere_one_finite :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1).Finite := by
  apply Set.Finite.subset ((Set.finite_singleton
      (EuclideanSpace.single (0 : Fin 1) (-1 : ℝ))).insert
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
  intro x hx
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_one] at hx
  simp only [Real.norm_eq_abs, sq_abs] at hx
  have h1 : x 0 ^ 2 = 1 := Real.sqrt_eq_one.mp hx
  have hxe : x = EuclideanSpace.single (0 : Fin 1) (x 0) := by
    ext i; fin_cases i; simp
  rcases mul_self_eq_one_iff.mp (by nlinarith [h1] : x 0 * x 0 = 1) with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl (by rw [hxe, h]))
  · exact Set.mem_insert_iff.mpr (Or.inr (by rw [Set.mem_singleton_iff, hxe, h]))

lemma sphere_one_coord (x : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    x.1 0 = 1 ∨ x.1 0 = -1 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 := norm_eq_of_mem_sphere x
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs,
    Real.sqrt_eq_one, sq_abs] at hx
  exact mul_self_eq_one_iff.mp (by nlinarith [hx])

lemma sphere_one_eq_single (x : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (x : EuclideanSpace ℝ (Fin 1)) =
      EuclideanSpace.single (0 : Fin 1) (x.1 0) := by
  ext i; fin_cases i; simp

noncomputable def sphereOneEquivBool :
    ↥(sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) ≃ Bool where
  toFun x := decide (x.1 0 = 1)
  invFun b := if b then ⟨EuclideanSpace.single 0 1, by simp⟩
    else ⟨EuclideanSpace.single 0 (-1), by simp⟩
  left_inv x := by
    apply Subtype.ext
    rcases sphere_one_coord x with h | h
    · have hb : decide (x.1 0 = 1) = true := by simp [h]
      simp only [hb, ↓reduceIte]
      rw [sphere_one_eq_single x, h]
    · have hb : decide (x.1 0 = 1) = false := by
        rw [decide_eq_false_iff_not, h]; norm_num
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rw [sphere_one_eq_single x, h]
  right_inv b := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [decide_eq_false_iff_not]
      simp
      norm_num
    · simp only [↓reduceIte]
      rw [decide_eq_true_eq]
      simp

lemma joined_eq_of_totallyDisconnected {X : Type u} [TopologicalSpace X]
    [TotallyDisconnectedSpace X] {a b : X} (h : Joined a b) : a = b := by
  obtain ⟨γ⟩ := h
  have hsub : (Set.range γ).Subsingleton := by
    have : IsPreconnected (Set.range γ) := by
      rw [← Set.image_univ]
      exact isPreconnected_univ.image γ γ.continuous.continuousOn
    exact this.subsingleton
  exact hsub ⟨0, γ.source⟩ ⟨1, γ.target⟩

def zerothHomotopyDiscreteEquiv {X : Type u} [TopologicalSpace X]
    [TotallyDisconnectedSpace X] :
    ZerothHomotopy X ≃ X where
  toFun := ZerothHomotopy.lift id
    (fun _ _ p => joined_eq_of_totallyDisconnected ⟨p⟩)
  invFun := ZerothHomotopy.mk
  left_inv := by
    intro q
    induction q using ZerothHomotopy.rec with
    | mk x => rfl
  right_inv x := rfl

instance finite_sphere_one :
    Finite ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  sphere_one_finite.to_subtype

instance : DiscreteTopology ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  Finite.instDiscreteTopology

noncomputable def metricSphereZeroHomeoBool :
    ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) ≃ₜ Bool :=
  Equiv.toHomeomorphOfDiscrete sphereOneEquivBool

noncomputable def sphereZeroHomeoBool : ↥(TopCat.sphere.{u} 0) ≃ₜ Bool := by
  dsimp only [TopCat.sphere, TopCat.diskBoundary]
  exact (Homeomorph.ulift.{u, 0}
      (X := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))).trans
    metricSphereZeroHomeoBool

noncomputable def sphereZeroEquivBool : ↥(TopCat.sphere.{u} 0) ≃ Bool := by
  dsimp only [TopCat.sphere, TopCat.diskBoundary]
  exact (Equiv.ulift.{u, 0}
      (α := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))).trans
    sphereOneEquivBool

instance : Finite ↥(TopCat.sphere.{u} 0) :=
  Finite.of_equiv _ sphereZeroEquivBool.symm

instance : DiscreteTopology ↥(TopCat.sphere.{u} 0) :=
  sphereZeroHomeoBool.symm.discreteTopology

instance totallyDisconnected_sphere_zero :
    TotallyDisconnectedSpace ↥(TopCat.sphere.{u} 0) :=
  Homeomorph.totallyDisconnectedSpace sphereZeroHomeoBool.symm

noncomputable def sphereZeroPi0Equiv :
    ZerothHomotopy ↥(TopCat.sphere.{u} 0) ≃ Bool :=
  zerothHomotopyDiscreteEquiv.trans sphereZeroEquivBool

noncomputable def sphereZeroBasept :
    TopCat.of PUnit ⟶ TopCat.sphere.{u} 0 :=
  TopCat.ofHom (ContinuousMap.const _ (ULift.up.{u, 0} (northPt 0)))

@[simp] lemma sphereOneEquivBool_northPt :
    sphereOneEquivBool (northPt 0) = true := by
  simp [sphereOneEquivBool, northPt]

@[simp] lemma sphereOneEquivBool_southPt :
    sphereOneEquivBool (southPt 0) = false := by
  simp only [sphereOneEquivBool, southPt]
  norm_num

@[simp] lemma sphereZeroHomeoBool_northPt :
    sphereZeroHomeoBool (ULift.up.{u, 0} (northPt 0)) = true := by
  dsimp only [sphereZeroHomeoBool, TopCat.sphere, TopCat.diskBoundary]
  change sphereOneEquivBool (northPt 0) = true
  exact sphereOneEquivBool_northPt

@[simp] lemma sphereZeroHomeoBool_southPt :
    sphereZeroHomeoBool (ULift.up.{u, 0} (southPt 0)) = false := by
  dsimp only [sphereZeroHomeoBool, TopCat.sphere, TopCat.diskBoundary]
  change sphereOneEquivBool (southPt 0) = false
  exact sphereOneEquivBool_southPt

@[simp] lemma sphereZeroHomeoBool_antipodal (x : ↥(TopCat.sphere.{u} 0)) :
    sphereZeroHomeoBool (sphereAntipodalHomeo 0 x) =
      !(sphereZeroHomeoBool x) := by
  cases hb : sphereZeroHomeoBool x with
  | true =>
    have hx : x = ULift.up (northPt 0) := by
      have h1 : sphereZeroHomeoBool.{u} x =
          sphereZeroHomeoBool.{u} (ULift.up.{u, 0} (northPt 0)) := by
        rw [hb, sphereZeroHomeoBool_northPt]
      exact sphereZeroHomeoBool.injective h1
    rw [hx, sphereAntipodalHomeo_northPt, sphereZeroHomeoBool_southPt]
    rfl
  | false =>
    have hx : x = ULift.up (southPt 0) := by
      have h1 : sphereZeroHomeoBool.{u} x =
          sphereZeroHomeoBool.{u} (ULift.up.{u, 0} (southPt 0)) := by
        rw [hb, sphereZeroHomeoBool_southPt]
      exact sphereZeroHomeoBool.injective h1
    rw [hx, sphereAntipodalHomeo_southPt, sphereZeroHomeoBool_northPt]
    rfl

@[simp] lemma sphereZeroHomeoBool_antipodalMap (x : ↥(TopCat.sphere.{u} 0)) :
    sphereZeroHomeoBool (sphereAntipodalMap 0 x) =
      !(sphereZeroHomeoBool x) := by
  rw [sphereAntipodalMap_apply, ← sphereAntipodalHomeo_apply,
    sphereZeroHomeoBool_antipodal]

end S0

end AlgebraicTopology
