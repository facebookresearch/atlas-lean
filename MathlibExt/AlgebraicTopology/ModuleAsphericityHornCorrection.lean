/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModuleAsphericityConsequences
public import MathlibExt.AlgebraicTopology.SimplicialSet.FibrationToConstant
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupKan
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# Horn correction for augmented simplicial modules

Every simplicial module over a ring has a Kan underlying simplicial set, and its
augmentation to a constant module is a fibration. A zeroth-horn lift therefore supplies
all prescribed positive faces and the specified augmentation value.

If the normalized augmentation is a quasi-isomorphism, the discrepancy in the missing
zero face has a normalized obstruction filler. Subtracting this filler corrects the
horn lift to a full boundary lift, preserving all other faces and the augmentation.
The construction applies in every positive simplex dimension and keeps the ring and
module-carrier universes independent.

See Loday, §3.5.3, and the Stacks Project, Tag 0194.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace AlgebraicTopology.ModuleResolutionAsphericity

variable {R : Type u} [Ring R]

/--
The underlying additive group of an `R`-module, written as a group, with module maps
sent to their underlying group homomorphisms.
-/
def moduleGroupFunctor : ModuleCat.{v} R ⥤ GrpCat.{v} :=
  forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙
    AddCommGrpCat.toCommGrp ⋙ forget₂ CommGrpCat.{v} GrpCat.{v}

/--
The underlying simplicial set of any simplicial `R`-module is a Kan complex.
-/
theorem underlying_module_isKan (X : SimplicialObject (ModuleCat.{v} R)) :
    SSet.KanComplex (X ⋙ forget (ModuleCat.{v} R)) := by
  let G := X ⋙ moduleGroupFunctor (R := R)
  have h := SSet.SimplicialGroupHorn.underlying_isKan G
  change SSet.KanComplex (X ⋙ forget (ModuleCat.{v} R)) at h
  exact h

variable (P : SimplicialObject.Augmented (ModuleCat.{v} R))

/--
The underlying simplicial-set augmentation of any augmented simplicial `R`-module
to its constant target is a fibration.
-/
theorem underlying_module_fibration : Fibration (underlying P).hom := by
  letI : SSet.KanComplex (underlying P).left := underlying_module_isKan P.left
  haveI : SSet.KanComplex ((𝟭 (SimplicialObject (Type v))).obj (underlying P).left) := by
    change SSet.KanComplex (underlying P).left
    exact underlying_module_isKan P.left
  exact SSet.fibration_to_constant (underlying P).hom

/--
Given a boundary map and a compatible augmentation simplex in dimension `n + 1`,
there is a simplex in the underlying simplicial module with every prescribed
nonzero face and the specified augmentation.
-/
theorem exists_original_hornZero_lift (n : ℕ)
    (a : (SSet.boundary.{v} (n + 1) : SSet.{v}) ⟶ (underlying P).left)
    (b : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶
      (SimplicialObject.const (Type v)).obj (P.right : Type v))
    (sq : CommSq a (SSet.boundary.{v} (n + 1)).ι (underlying P).hom b) :
    ∃ φ : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶ (underlying P).left,
      (∀ (j : Fin (n + 2)) (_ : j ≠ 0),
        SSet.stdSimplex.δ j ≫ φ = SSet.boundary.ι j ≫ a) ∧
          φ ≫ (underlying P).hom = b := by
  let l := SSet.Subcomplex.homOfLE (SSet.horn_zero_le_boundary.{v} n)
  let top := l ≫ a
  have hs : CommSq top (SSet.horn.{v} (n + 1) 0).ι (underlying P).hom b := by
    refine ⟨?_⟩
    change (l ≫ a) ≫ (underlying P).hom = _
    exact (Category.assoc l a (underlying P).hom).trans
      ((congrArg (fun f => l ≫ f) sq.w).trans
        ((Category.assoc l (SSet.boundary.{v} (n + 1)).ι b).symm.trans
          (congrArg (fun f => f ≫ b) (SSet.Subcomplex.homOfLE_ι _))))
  letI : Fibration (underlying P).hom := underlying_module_fibration P
  let hLP : HasLiftingProperty (SSet.horn.{v} (n + 1) 0).ι (underlying P).hom :=
    inferInstance
  letI : hs.HasLift := hLP.sq_hasLift hs
  let φ := hs.lift
  refine ⟨φ, ?_, hs.fac_right⟩
  intro j hj
  have hinc : SSet.horn.ι (0 : Fin (n + 2)) j hj ≫ l = SSet.boundary.ι j := by
    apply (cancel_mono (SSet.boundary.{v} (n + 1)).ι).mp
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.horn.ι_ι, SSet.boundary.ι_ι]
  calc
    _ = (SSet.horn.ι (0 : Fin (n + 2)) j hj ≫
        (SSet.horn.{v} (n + 1) 0).ι) ≫ φ := by rw [SSet.horn.ι_ι]
    _ = SSet.horn.ι (0 : Fin (n + 2)) j hj ≫ top := by rw [Category.assoc, hs.fac_left]
    _ = _ := by change _ ≫ (l ≫ a) = _; rw [← Category.assoc, hinc]

variable [QuasiIso (augmentation P)]

/--
For an additively aspherical augmentation, a simplex matching all positive faces and
the augmentation of a boundary square can be corrected to match the missing zero
face as well, while preserving those positive faces and the augmentation.
-/
theorem correct_original_hornZero (n : ℕ)
    (a : (SSet.boundary.{v} (n + 1) : SSet.{v}) ⟶ (underlying P).left)
    (b : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶
      (SimplicialObject.const (Type v)).obj (P.right : Type v))
    (sq : CommSq a (SSet.boundary.{v} (n + 1)).ι (underlying P).hom b)
    (φ : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶ (underlying P).left)
    (hfaces : ∀ (j : Fin (n + 2)) (_ : j ≠ 0),
      SSet.stdSimplex.δ j ≫ φ = SSet.boundary.ι j ≫ a)
    (hpoint : φ ≫ (underlying P).hom = b) :
    ∃ ψ : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶ (underlying P).left,
      (∀ j : Fin (n + 2), SSet.stdSimplex.δ j ≫ ψ = SSet.boundary.ι j ≫ a) ∧
        ψ ≫ (underlying P).hom = b := by
  let y : P.left.obj (op ⦋n + 1⦌) := SSet.yonedaEquiv φ
  let f : Fin (n + 2) → P.left.obj (op ⦋n⦌) := fun j =>
    SSet.yonedaEquiv (SSet.boundary.ι j ≫ a)
  let x : P.left.obj (op ⦋n⦌) := (P.left.δ (0 : Fin (n + 2))).hom y - f 0
  have hy : ∀ j : Fin (n + 1), (P.left.δ j.succ).hom y = f j.succ := by
    intro j
    have h := congrArg SSet.yonedaEquiv (hfaces j.succ (Fin.succ_ne_zero j))
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp] at h
    exact h
  have hxpoint : (P.hom.app (op ⦋n⦌)).hom x = 0 := by
    have hφ : (SSet.stdSimplex.δ (0 : Fin (n + 2)) ≫ φ) ≫ (underlying P).hom =
        SSet.stdSimplex.δ (0 : Fin (n + 2)) ≫ b :=
      (Category.assoc _ _ _).trans (congrArg (fun f => SSet.stdSimplex.δ (0 : Fin (n + 2)) ≫ f) hpoint)
    have ha : (SSet.boundary.ι (0 : Fin (n + 2)) ≫ a) ≫ (underlying P).hom =
        SSet.stdSimplex.δ (0 : Fin (n + 2)) ≫ b := by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => SSet.boundary.ι (0 : Fin (n + 2)) ≫ f) sq.w).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun f => f ≫ b) (SSet.boundary.ι_ι (0 : Fin (n + 2))))))
    have hφv := congrArg SSet.yonedaEquiv hφ
    have hav := congrArg SSet.yonedaEquiv ha
    rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_δ_comp] at hφv
    rw [SSet.yonedaEquiv_comp] at hav
    change (P.hom.app (op ⦋n⦌)).hom ((P.left.δ (0 : Fin (n + 2))).hom y) = _ at hφv
    change (P.hom.app (op ⦋n⦌)).hom (f 0) = _ at hav
    dsimp only [x]
    rw [map_sub, hφv, hav]
    exact sub_self _
  obtain ⟨z, hz0, hzpos, hzpoint⟩ : ∃ z : P.left.obj (op ⦋n + 1⦌),
      (P.left.δ (0 : Fin (n + 2))).hom z = x ∧
        (∀ j : Fin (n + 1), (P.left.δ j.succ).hom z = 0) ∧
          (P.hom.app (op ⦋n + 1⦌)).hom z = 0 := by
    cases n with
    | zero =>
      obtain ⟨z, hz0, hz1, hzp⟩ := original_zero_obstruction_filler_of_quasiIso P x hxpoint
      refine ⟨z, hz0, ?_, hzp⟩
      intro j
      have hj : j = 0 := Fin.ext (by have h := j.isLt; simp only [Nat.zero_add] at h; omega)
      subst j
      exact hz1
    | succ n =>
      have hx : ∀ i : Fin (n + 2), (P.left.δ i).hom x = 0 := by
        intro i
        have hc := (SSet.boundary.isCompatible_succ_iff _).mp
          (SSet.boundary_isCompatible_of_hom a) 0 i.succ (Fin.succ_pos i)
        have hcv := congrArg SSet.yonedaEquiv hc
        simp only [SSet.stdSimplex.yonedaEquiv_δ_comp, Fin.pred_succ] at hcv
        change (P.left.δ i).hom (f 0) =
          (P.left.δ (0 : Fin (n + 2))).hom (f i.succ) at hcv
        have hd := congrArg (fun h => h.hom y) (P.left.δ_comp_δ (Fin.zero_le i))
        change (P.left.δ (0 : Fin (n + 2))).hom ((P.left.δ i.succ).hom y) =
          (P.left.δ i).hom ((P.left.δ (0 : Fin (n + 3))).hom y) at hd
        dsimp only [x]
        rw [map_sub, ← hd, hy, ← hcv, sub_self]
      exact original_positive_obstruction_filler_of_quasiIso P n x hx
  let ψ : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶ (underlying P).left :=
    SSet.yonedaEquiv.symm (y - z)
  refine ⟨ψ, ?_, ?_⟩
  · intro j
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    change (P.left.δ j).hom (SSet.yonedaEquiv ψ) = f j
    have hψ : SSet.yonedaEquiv ψ = (y - z : P.left.obj (op ⦋n + 1⦌)) :=
      (SSet.yonedaEquiv (X := (underlying P).left) (n := ⦋n + 1⦌)).apply_symm_apply _
    rw [hψ]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [map_sub, hz0]
      dsimp only [x]
      exact sub_sub_cancel _ _
    · rw [map_sub, hzpos j, sub_zero]
      exact hy j
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change (P.hom.app (op ⦋n + 1⦌)).hom (SSet.yonedaEquiv ψ) = SSet.yonedaEquiv b
    have hψ : SSet.yonedaEquiv ψ = (y - z : P.left.obj (op ⦋n + 1⦌)) :=
      (SSet.yonedaEquiv (X := (underlying P).left) (n := ⦋n + 1⦌)).apply_symm_apply _
    rw [hψ]
    have hp := congrArg SSet.yonedaEquiv hpoint
    rw [SSet.yonedaEquiv_comp] at hp
    change (P.hom.app (op ⦋n + 1⦌)).hom y = SSet.yonedaEquiv b at hp
    rw [map_sub, hp, hzpoint, sub_zero]

/--
If the normalized augmentation is a quasi-isomorphism, every compatible boundary
square in dimension `n + 1` has a simplex lift whose boundary and augmentation are
exactly the specified maps.
-/
theorem exists_original_boundary_lift_of_quasiIso (n : ℕ)
    (a : (SSet.boundary.{v} (n + 1) : SSet.{v}) ⟶ (underlying P).left)
    (b : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶
      (SimplicialObject.const (Type v)).obj (P.right : Type v))
    (sq : CommSq a (SSet.boundary.{v} (n + 1)).ι (underlying P).hom b) :
    ∃ ψ : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶ (underlying P).left,
      (SSet.boundary.{v} (n + 1)).ι ≫ ψ = a ∧ ψ ≫ (underlying P).hom = b := by
  obtain ⟨φ, hfaces, hpoint⟩ := exists_original_hornZero_lift P n a b sq
  obtain ⟨ψ, hψ, hψpoint⟩ := correct_original_hornZero P n a b sq φ hfaces hpoint
  refine ⟨ψ, ?_, hψpoint⟩
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι]
  exact hψ j

end AlgebraicTopology.ModuleResolutionAsphericity

end
