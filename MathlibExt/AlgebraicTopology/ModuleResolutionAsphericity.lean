/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModuleMooreComplex
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentationQuasiIso
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedChainHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.SliceLeftFibration
public import MathlibExt.AlgebraicTopology.SimplicialObject.SliceTrivialFibration
public import MathlibExt.AlgebraicTopology.SimplicialObject.RightExtraDegeneracyHomotopy
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Module normalization of a simplicial trivial fibration

Let `P → const M` be an augmented simplicial module over a ring `R`. If its
underlying simplicial-set augmentation is a trivial fibration, compatible boundaries
with augmentation zero have module-valued lifts. In particular, positive normalized
cycles and degree-zero augmentation-kernel elements are boundaries.

The normalized complex therefore has zero positive homology, and its degree-zero
homology is naturally isomorphic to `M`, with the isomorphism sending a class to its
augmentation. The normalized augmentation to `M` concentrated in degree zero is a
quasi-isomorphism. All comparison maps commute with augmented module maps, and the
ring and module-carrier universes are independent.

See the Stacks Project, Tag 0194 and §§92.3–92.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace AlgebraicTopology.ModuleResolutionAsphericity

open ModuleMooreComplex

variable {R : Type u} [Ring R]
  (P : SimplicialObject.Augmented (ModuleCat.{v} R))

/--
The augmented simplicial set obtained by forgetting the module structure from the
diagram, augmentation target, and augmentation map of `P`.
-/
abbrev underlying : SimplicialObject.Augmented (Type v) :=
  ((SimplicialObject.Augmented.whiskering (ModuleCat.{v} R) (Type v)).obj
    (forget (ModuleCat.{v} R))).obj P

/--
The normalized Moore chain complex of the simplicial module diagram `P.left`.
-/
abbrev normalized : ChainComplex (ModuleCat.{v} R) ℕ :=
  (normalizedMooreComplex (ModuleCat.{v} R)).obj P.left

/--
If the underlying augmentation is a trivial fibration, a compatible family of
`n + 2` degree-`n` faces with augmentation zero has a degree-`n + 1` module lift
with exactly those faces and augmentation zero.
-/
theorem exists_module_boundary_lift
    (hp : trivialFibrations SSet.{v} (underlying P).hom) (n : ℕ)
    (faces : Fin (n + 2) → P.left.obj (op ⦋n⦌))
    (hf : SSet.boundary.IsCompatible
      (fun j => (SSet.yonedaEquiv (X := (underlying P).left)).symm (faces j)))
    (hpoint : ∀ j, (P.hom.app (op ⦋n⦌)).hom (faces j) = 0) :
    ∃ y : P.left.obj (op ⦋n + 1⦌),
      (∀ j : Fin (n + 2), (P.left.δ j).hom y = faces j) ∧
        (P.hom.app (op ⦋n + 1⦌)).hom y = 0 := by
  letI : Fibration (underlying P).hom := (mem_trivialFibrations_iff _).mp hp |>.1
  letI : WeakEquivalence (underlying P).hom := (mem_trivialFibrations_iff _).mp hp |>.2
  letI : Cofibration (SSet.boundary.{v} (n + 1)).ι :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  let hLift : HasLiftingProperty (SSet.boundary.{v} (n + 1)).ι (underlying P).hom :=
    ModelCategory.cm4b _ _
  let b : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶
      (SimplicialObject.const (Type v)).obj (P.right : Type v) :=
    SSet.yonedaEquiv.symm (0 : P.right)
  have hcomm : ∀ j : Fin (n + 2),
      SSet.yonedaEquiv.symm (faces j) ≫ (underlying P).hom = SSet.stdSimplex.δ j ≫ b := by
    intro j
    let Z := (SimplicialObject.const (Type v)).obj (P.right : Type v)
    let x : (underlying P).left.obj (op ⦋n⦌) := faces j
    have hL := SSet.yonedaEquiv_symm_comp x (underlying P).hom
    have hB := SSet.stdSimplex.δ_comp_yonedaEquiv_symm
      (X := Z) (n := n) (0 : P.right) j
    let z : ((SimplicialObject.const (Type v)).obj (underlying P).right).obj (op ⦋n⦌) :=
      (0 : P.right)
    have hpj : (underlying P).hom.app (op ⦋n⦌) x = z := hpoint j
    have hM := congrArg (SSet.yonedaEquiv (X := Z) (n := ⦋n⦌)).symm hpj
    have hB' : SSet.stdSimplex.δ j ≫ b =
        (SSet.yonedaEquiv (X := Z) (n := ⦋n⦌)).symm (0 : P.right) := hB
    exact hL.trans (hM.trans hB'.symm)
  obtain ⟨φ, hφ, hφpoint⟩ := SSet.exists_simplex_lift_boundary hf hLift b hcomm
  refine ⟨SSet.yonedaEquiv φ, ?_, ?_⟩
  · intro j
    have h := congrArg (SSet.yonedaEquiv (X := (underlying P).left) (n := ⦋n⦌)) (hφ j)
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp] at h
    have he := (SSet.yonedaEquiv (X := (underlying P).left) (n := ⦋n⦌)).apply_symm_apply
      (show (underlying P).left.obj (op ⦋n⦌) from faces j)
    exact h.trans he
  · let Z := (SimplicialObject.const (Type v)).obj (P.right : Type v)
    have h := congrArg (SSet.yonedaEquiv (X := Z) (n := ⦋n + 1⦌)) hφpoint
    have hC := SSet.yonedaEquiv_comp φ (underlying P).hom
    have he := (SSet.yonedaEquiv (X := Z) (n := ⦋n + 1⦌)).apply_symm_apply (0 : P.right)
    exact hC.symm.trans (h.trans he)

/--
Under the underlying trivial-fibration condition, any `x ∈ P₀` with augmentation
zero has an edge `y ∈ P₁` with `d₀ y = x` and `d₁ y = 0`.
-/
theorem exists_zero_boundary
    (hp : trivialFibrations SSet.{v} (underlying P).hom)
    (x : P.left.obj (op ⦋0⦌)) (hx : (P.hom.app (op ⦋0⦌)).hom x = 0) :
    ∃ y : P.left.obj (op ⦋1⦌),
      (P.left.δ (0 : Fin 2)).hom y = x ∧ (P.left.δ (1 : Fin 2)).hom y = 0 := by
  let faces : Fin 2 → P.left.obj (op ⦋0⦌) := fun j => if j = 0 then x else 0
  have hf : SSet.boundary.IsCompatible
      (fun j => (SSet.yonedaEquiv (X := (underlying P).left)).symm (faces j)) := by
    trivial
  have hpoint : ∀ j, (P.hom.app (op ⦋0⦌)).hom (faces j) = 0 := by
    intro j
    by_cases h : j = 0
    · subst j; exact hx
    · change (P.hom.app (op ⦋0⦌)).hom (if j = 0 then x else 0) = 0
      rw [if_neg h, map_zero]
  obtain ⟨y, hy, -⟩ := exists_module_boundary_lift P hp 0 faces hf hpoint
  exact ⟨y, by simpa only [faces, if_pos rfl] using hy 0,
    by simpa only [faces, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hy 1⟩

/--
Under the underlying trivial-fibration condition, an element `x ∈ P_(n+1)` with
all faces zero has a lift `y ∈ P_(n+2)` with zero face `x` and all positive faces zero.
-/
theorem exists_positive_boundary
    (hp : trivialFibrations SSet.{v} (underlying P).hom) (n : ℕ)
    (x : P.left.obj (op ⦋n + 1⦌))
    (hx : ∀ j : Fin (n + 2), (P.left.δ j).hom x = 0) :
    ∃ y : P.left.obj (op ⦋n + 2⦌),
      (P.left.δ (0 : Fin (n + 3))).hom y = x ∧
        ∀ j : Fin (n + 2), (P.left.δ j.succ).hom y = 0 := by
  let faces : Fin (n + 3) → P.left.obj (op ⦋n + 1⦌) := fun j => if j = 0 then x else 0
  have hf : SSet.boundary.IsCompatible
      (fun j => (SSet.yonedaEquiv (X := (underlying P).left)).symm (faces j)) := by
    rw [SSet.boundary.isCompatible_succ_iff]
    intro j k hjk
    have hk : k ≠ 0 := Fin.ne_zero_of_lt hjk
    by_cases hj : j = 0
    · simp only [faces, if_pos hj, if_neg hk]
      let x' : (underlying P).left.obj (op ⦋n + 1⦌) := x
      let z : (underlying P).left.obj (op ⦋n + 1⦌) := (0 : P.left.obj (op ⦋n + 1⦌))
      have hL := SSet.stdSimplex.δ_comp_yonedaEquiv_symm x' (k.pred (Fin.ne_zero_of_lt hjk))
      have hR := SSet.stdSimplex.δ_comp_yonedaEquiv_symm z (j.castPred (Fin.ne_last_of_lt hjk))
      have hzero : ((underlying P).left.δ (k.pred (Fin.ne_zero_of_lt hjk))) x' =
          ((underlying P).left.δ (j.castPred (Fin.ne_last_of_lt hjk))) z := by
        change (P.left.δ (k.pred (Fin.ne_zero_of_lt hjk))).hom x =
          (P.left.δ (j.castPred (Fin.ne_last_of_lt hjk))).hom 0
        rw [hx, map_zero]
      exact hL.trans ((congrArg (SSet.yonedaEquiv (X := (underlying P).left)).symm hzero).trans hR.symm)
    · simp only [faces, if_neg hj, if_neg hk]
      let z : (underlying P).left.obj (op ⦋n + 1⦌) := (0 : P.left.obj (op ⦋n + 1⦌))
      have hL := SSet.stdSimplex.δ_comp_yonedaEquiv_symm z (k.pred (Fin.ne_zero_of_lt hjk))
      have hR := SSet.stdSimplex.δ_comp_yonedaEquiv_symm z (j.castPred (Fin.ne_last_of_lt hjk))
      have hzero : ((underlying P).left.δ (k.pred (Fin.ne_zero_of_lt hjk))) z =
          ((underlying P).left.δ (j.castPred (Fin.ne_last_of_lt hjk))) z := by
        change (P.left.δ (k.pred (Fin.ne_zero_of_lt hjk))).hom 0 =
          (P.left.δ (j.castPred (Fin.ne_last_of_lt hjk))).hom 0
        rw [map_zero, map_zero]
      exact hL.trans ((congrArg (SSet.yonedaEquiv (X := (underlying P).left)).symm hzero).trans hR.symm)
  have hpx : (P.hom.app (op ⦋n + 1⦌)).hom x = 0 := by
    have h := congrArg (fun h => h.hom x)
      (P.hom.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op)
    change (P.hom.app (op ⦋n⦌)).hom ((P.left.δ (0 : Fin (n + 2))).hom x) =
      (P.hom.app (op ⦋n + 1⦌)).hom x at h
    rw [hx, map_zero] at h
    exact h.symm
  have hpoint : ∀ j, (P.hom.app (op ⦋n + 1⦌)).hom (faces j) = 0 := by
    intro j
    by_cases h : j = 0
    · subst j; exact hpx
    · change (P.hom.app (op ⦋n + 1⦌)).hom (if j = 0 then x else 0) = 0
      rw [if_neg h, map_zero]
  obtain ⟨y, hy, -⟩ := exists_module_boundary_lift P hp (n + 1) faces hf hpoint
  refine ⟨y, by simpa only [faces, if_pos rfl] using hy 0, ?_⟩
  intro j
  simpa only [faces, if_neg (Fin.succ_ne_zero j)] using hy j.succ

/--
Every normalized cycle in degree `n + 1` is the differential of an element in
normalized degree `n + 2`, if the underlying augmentation is a trivial fibration.
-/
theorem normalized_cycle_boundary
    (hp : trivialFibrations SSet.{v} (underlying P).hom) (n : ℕ)
    (x : (normalized P).X (n + 1)) (hx : ((normalized P).d (n + 1) n).hom x = 0) :
    ∃ y : (normalized P).X (n + 2), ((normalized P).d (n + 2) (n + 1)).hom y = x := by
  let x' := termEquiv P.left (n + 1) x
  have hpos : ∀ j : Fin (n + 1), (P.left.δ j.succ).hom x'.val = 0 :=
    (mem_normalizedSubmodule P.left n x'.val).mp x'.property
  have hzero : (P.left.δ (0 : Fin (n + 2))).hom x'.val = 0 := by
    have h := termEquiv_d_value P.left n x
    rw [hx, map_zero] at h
    exact h.symm
  have hfaces : ∀ j : Fin (n + 2), (P.left.δ j).hom x'.val = 0 :=
    fun j => Fin.cases hzero hpos j
  obtain ⟨y, hy, hnorm⟩ := exists_positive_boundary P hp n x'.val hfaces
  let y' : normalizedSubmodule P.left (n + 2) :=
    ⟨y, (mem_normalizedSubmodule P.left (n + 1) y).mpr hnorm⟩
  refine ⟨(termEquiv P.left (n + 2)).symm y', ?_⟩
  apply (termEquiv P.left (n + 1)).injective
  apply Subtype.ext
  rw [termEquiv_d_value, LinearEquiv.apply_symm_apply]
  exact hy

/--
The normalized complex is exact at every positive degree `n + 1`, under the
underlying trivial-fibration condition.
-/
theorem normalized_exactAt_positive
    (hp : trivialFibrations SSet.{v} (underlying P).hom) (n : ℕ) :
    (normalized P).ExactAt (n + 1) := by
  apply ((normalized P).exactAt_iff' (i := n + 2) (j := n + 1) (k := n)
    (by simp) (by simp)).mpr
  exact (ShortComplex.moduleCat_exact_iff _).mpr (normalized_cycle_boundary P hp n)

/--
The normalized homology in each positive degree `n + 1` is zero, if the underlying
augmentation is a trivial fibration.
-/
theorem normalized_homology_isZero_positive
    (hp : trivialFibrations SSet.{v} (underlying P).hom) (n : ℕ) :
    IsZero ((normalized P).homology (n + 1)) :=
  (normalized_exactAt_positive P hp n).isZero_homology

/--
The chain map from the normalized complex to the augmentation target in degree zero,
given by the normalized inclusion followed by the alternating-face augmentation.
-/
def augmentation : normalized P ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj P.right :=
  inclusionOfMooreComplexMap P.left ≫ AlternatingFaceMapComplex.ε.app P

/--
The degree-zero component of the normalized augmentation is the normalized inclusion
into `P₀` followed by the degree-zero simplicial augmentation.
-/
@[simp]
theorem augmentation_zero : (augmentation P).f 0 =
    (inclusionOfMooreComplexMap P.left).f 0 ≫ P.hom.app (op ⦋0⦌) := by
  rw [augmentation, HomologicalComplex.comp_f, AlternatingFaceMapComplex.ε_app_f_zero]
  rfl

/--
If the underlying augmentation is a trivial fibration, its degree-zero normalized
augmentation map is surjective.
-/
theorem augmentation_zero_surjective
    (hp : trivialFibrations SSet.{v} (underlying P).hom) :
    Function.Surjective ((augmentation P).f 0).hom := by
  intro a
  let E := SSet.SplitHomotopyEquivOver.ofTrivialFibration (underlying P).hom hp
  let x := E.section_.app (op ⦋0⦌) a
  refine ⟨(termEquiv P.left 0).symm ⟨x, Submodule.mem_top⟩, ?_⟩
  rw [augmentation_zero]
  change (P.hom.app (op ⦋0⦌)).hom
    (((inclusionOfMooreComplexMap P.left).f 0).hom
      ((termEquiv P.left 0).symm ⟨x, Submodule.mem_top⟩)) = a
  rw [termEquiv_symm_value]
  exact congrArg (fun h => h.app (op ⦋0⦌) a) E.section_comp

/--
An element in normalized degree zero with augmentation zero is the differential of
an element in normalized degree one, under the underlying trivial-fibration condition.
-/
theorem augmentation_zero_kernel_boundary
    (hp : trivialFibrations SSet.{v} (underlying P).hom)
    (x : (normalized P).X 0) (hx : ((augmentation P).f 0).hom x = 0) :
    ∃ y : (normalized P).X 1, ((normalized P).d 1 0).hom y = x := by
  let x' := termEquiv P.left 0 x
  have hpx : (P.hom.app (op ⦋0⦌)).hom x'.val = 0 := by
    have h := (congrArg (fun f => f.hom x) (augmentation_zero P)).symm.trans hx
    change (P.hom.app (op ⦋0⦌)).hom
      (((inclusionOfMooreComplexMap P.left).f 0).hom x) = 0 at h
    exact h
  obtain ⟨y, hy, hnorm⟩ := exists_zero_boundary P hp x'.val hpx
  let y' : normalizedSubmodule P.left 1 := ⟨y, (mem_normalizedSubmodule P.left 0 y).mpr
    (by
      intro j
      have hj : j = 0 := by
        apply Fin.ext
        have hlt := j.isLt
        change j.val < 1 at hlt
        change j.val = 0
        omega
      subst j
      exact hnorm)⟩
  refine ⟨(termEquiv P.left 1).symm y', ?_⟩
  apply (termEquiv P.left 0).injective
  apply Subtype.ext
  rw [termEquiv_d_value, LinearEquiv.apply_symm_apply]
  exact hy

/--
Under the underlying trivial-fibration condition, the image of the normalized
differential `N₁(P) → N₀(P)` is the kernel of the normalized augmentation to `M`.
-/
theorem augmentation_zero_exact
    (hp : trivialFibrations SSet.{v} (underlying P).hom) :
    Function.Exact ((normalized P).d 1 0).hom ((augmentation P).f 0).hom := by
  apply LinearMap.exact_iff.mpr
  apply le_antisymm
  · intro x hx
    exact augmentation_zero_kernel_boundary P hp x hx
  · apply LinearMap.range_le_ker_iff.mpr
    exact ModuleCat.hom_ext_iff.mp
      ((ChainComplex.toSingle₀Equiv (normalized P) P.right) (augmentation P)).property

/--
The isomorphism from normalized degree-zero homology to the augmentation target
`M`, constructed under the underlying trivial-fibration condition.
-/
def homologyZeroIso (hp : trivialFibrations SSet.{v} (underlying P).hom) :
    (normalized P).homology 0 ≅ P.right :=
  IsColimit.coconePointUniqueUpToIso
    (ChainComplex.homologyZeroCoforkIsColimit (normalized P))
    (ModuleCat.isColimitCokernelCofork ((normalized P).d 1 0) ((augmentation P).f 0)
      (augmentation_zero_exact P hp) (augmentation_zero_surjective P hp))

/--
The degree-zero class map followed by `homologyZeroIso` equals the normalized
augmentation map.
-/
@[reassoc (attr := simp)]
theorem homologyZeroIso_class (hp : trivialFibrations SSet.{v} (underlying P).hom) :
    ChainComplex.homologyZeroClass (normalized P) ≫ (homologyZeroIso P hp).hom =
      (augmentation P).f 0 :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (ChainComplex.homologyZeroCoforkIsColimit (normalized P))
    (ModuleCat.isColimitCokernelCofork ((normalized P).d 1 0) ((augmentation P).f 0)
      (augmentation_zero_exact P hp) (augmentation_zero_surjective P hp))
    WalkingParallelPair.one

variable {P} {Q : SimplicialObject.Augmented (ModuleCat.{v} R)}

/--
For an augmented module map `f : P ⟶ Q`, the degree-zero normalized map followed
by the augmentation of `Q` equals the augmentation of `P` followed by `f.right`.
-/
@[reassoc]
theorem augmentation_zero_naturality (f : P ⟶ Q) :
    ((normalizedMooreComplex (ModuleCat.{v} R)).map f.left).f 0 ≫ (augmentation Q).f 0 =
      (augmentation P).f 0 ≫ f.right := by
  have h := congrArg (fun h => h.f 0)
    ((inclusionOfMooreComplex (ModuleCat.{v} R)).naturality f.left)
  change _ ≫ (inclusionOfMooreComplexMap Q.left).f 0 =
    (inclusionOfMooreComplexMap P.left).f 0 ≫ f.left.app (op ⦋0⦌) at h
  have hP : f.left.app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) =
      P.hom.app (op ⦋0⦌) ≫ f.right := NatTrans.congr_app f.w (op ⦋0⦌)
  exact (congrArg (fun g => ((normalizedMooreComplex (ModuleCat.{v} R)).map f.left).f 0 ≫ g)
    (augmentation_zero Q)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ Q.hom.app (op ⦋0⦌)) h).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun g => (inclusionOfMooreComplexMap P.left).f 0 ≫ g) hP).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun g => g ≫ f.right) (augmentation_zero P).symm))))))

/--
For an augmented map between two diagrams satisfying the underlying
trivial-fibration condition, the degree-zero homology comparisons commute with the
normalized homology map and the map of augmentation targets.
-/
@[reassoc]
theorem homologyZeroIso_naturality (f : P ⟶ Q)
    (hp : trivialFibrations SSet.{v} (underlying P).hom)
    (hq : trivialFibrations SSet.{v} (underlying Q).hom) :
    HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} R)).map f.left) 0 ≫
      (homologyZeroIso Q hq).hom = (homologyZeroIso P hp).hom ≫ f.right := by
  apply Cofork.IsColimit.hom_ext (ChainComplex.homologyZeroCoforkIsColimit (normalized P))
  change ChainComplex.homologyZeroClass (normalized P) ≫ (_ ≫ _) =
    ChainComplex.homologyZeroClass (normalized P) ≫ (_ ≫ _)
  rw [← Category.assoc, ChainComplex.homologyZeroClass_naturality, Category.assoc,
    homologyZeroIso_class, ← Category.assoc, homologyZeroIso_class]
  exact augmentation_zero_naturality f

variable (P)

/--
The augmented simplicial module map from `P` to the constant augmented diagram on
its target, with left component the augmentation and right component the identity.
-/
def toConstant : P ⟶ (SimplicialObject.Augmented.const (C := ModuleCat.{v} R)).obj P.right :=
  SimplicialObject.Augmented.augmentationToConstant P

/--
The underlying augmentation of the constant augmented module on `M` is a
trivial fibration.
-/
theorem constant_condition (M : ModuleCat.{v} R) :
    trivialFibrations SSet.{v}
      (underlying ((SimplicialObject.Augmented.const (C := ModuleCat.{v} R)).obj M)).hom := by
  change trivialFibrations SSet.{v} (𝟙 ((SimplicialObject.const (Type v)).obj (M : Type v)))
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

/--
The normalized chain map induced by the simplicial augmentation
`P.left → const P.right`.
-/
def normalizationMap : normalized P ⟶
    normalized ((SimplicialObject.Augmented.const (C := ModuleCat.{v} R)).obj P.right) :=
  (normalizedMooreComplex (ModuleCat.{v} R)).map P.hom

/--
If the underlying augmentation is a trivial fibration, its normalized map to the
constant target module diagram is a quasi-isomorphism.
-/
theorem normalizationMap_quasiIso
    (hp : trivialFibrations SSet.{v} (underlying P).hom) : QuasiIso (normalizationMap P) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let E := homologyZeroIso P hp
    let E' := homologyZeroIso
      ((SimplicialObject.Augmented.const (C := ModuleCat.{v} R)).obj P.right)
      (constant_condition P.right)
    have h := homologyZeroIso_naturality (toConstant P) hp (constant_condition P.right)
    change HomologicalComplex.homologyMap (normalizationMap P) 0 ≫ E'.hom = E.hom ≫ 𝟙 _ at h
    rw [Category.comp_id] at h
    have he : HomologicalComplex.homologyMap (normalizationMap P) 0 = E.hom ≫ E'.inv := by
      apply (cancel_mono E'.hom).mp
      have hE : (E.hom ≫ E'.inv) ≫ E'.hom = E.hom :=
        (Category.assoc E.hom E'.inv E'.hom).trans
          ((congrArg (fun f => E.hom ≫ f) E'.inv_hom_id).trans (Category.comp_id _))
      exact h.trans hE.symm
    rw [he]
    exact (E ≪≫ E'.symm).isIso_hom
  | succ n =>
    apply (quasiIsoAt_iff_exactAt (normalizationMap P) (n + 1)
      (normalized_exactAt_positive P hp n)).mpr
    exact normalized_exactAt_positive _ (constant_condition P.right) n

/--
The normalized augmentation of the constant simplicial module on `M` to `M` in
degree zero is a quasi-isomorphism.
-/
theorem constant_augmentation_quasiIso (M : ModuleCat.{v} R) :
    QuasiIso (augmentation ((SimplicialObject.Augmented.const (C := ModuleCat.{v} R)).obj M)) :=
  ((DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := (SimplicialObject.const (ModuleCat.{v} R)).obj M)).trans
      (SimplicialObject.Augmented.constantRightExtraDegeneracy M).homotopyEquiv).quasiIso_hom

/--
The normalized map to the constant target diagram, followed by that diagram's
normalized augmentation, is the normalized augmentation of `P`.
-/
theorem normalizationMap_augmentation :
    normalizationMap P ≫
      augmentation ((SimplicialObject.Augmented.const (C := ModuleCat.{v} R)).obj P.right) =
        augmentation P := by
  exact SimplicialObject.normalized_augmentation_to_constant P

/--
If the underlying simplicial-set augmentation is a trivial fibration, the normalized
module augmentation is a quasi-isomorphism.
-/
theorem augmentation_quasiIso
    (hp : trivialFibrations SSet.{v} (underlying P).hom) : QuasiIso (augmentation P) := by
  letI : QuasiIso (normalizationMap P) := normalizationMap_quasiIso P hp
  letI : QuasiIso
      (augmentation ((SimplicialObject.Augmented.const (C := ModuleCat.{v} R)).obj P.right)) :=
    constant_augmentation_quasiIso P.right
  have h := normalizationMap_augmentation P
  dsimp only [SimplicialObject.Augmented.const] at h
  exact h ▸ (inferInstance : QuasiIso (normalizationMap P ≫
    augmentation ((SimplicialObject.Augmented.const (C := ModuleCat.{v} R)).obj P.right)))

end AlgebraicTopology.ModuleResolutionAsphericity

end
