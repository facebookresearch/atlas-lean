/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompactSupportBetti
public import MathlibExt.AlgebraicGeometry.CoefficientBettiModels

/-!
# The actual compact-support constructions over a specified coefficient field

This is the coefficient-field extension of the completed native rational
compact-support construction. Sections are the actual submodule with
compact nonzero-germ closure. Its derived functor and dualizing Hom
representation fix compact-support trace, including its scalar action.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoefficientCompactSupportModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.TopologicalSpace
open _root_.TopCat
open ConstructibleComplexes CoefficientBettiModels
attribute [local instance] HasDerivedCategory.standard

variable (k : Type) [Field k] {Z : TopCat.{0}}

abbrev GlobalSections (F : CoefficientSheaf k Z) := F.presheaf.obj (op (⊤ : Opens Z))

def germSupport (F : CoefficientSheaf k Z) (s : GlobalSections k F) : Set Z :=
  {x | F.presheaf.germ ⊤ x (by trivial) s ≠ 0}

def compactSections (F : CoefficientSheaf k Z) : Submodule k (GlobalSections k F) where
  carrier := {s | IsCompact (closure (germSupport k F s))}
  zero_mem' := by simp [germSupport]
  add_mem' := by
    intro s t hs ht
    have hsub : germSupport k F (s+t) ⊆ germSupport k F s ∪ germSupport k F t := by
      intro x hx
      by_contra h
      simp only [Set.mem_union, not_or, germSupport, Set.mem_ofPred_eq, ne_eq, not_not] at h
      exact hx (by simp [map_add, h.1, h.2])
    exact (hs.union ht).of_isClosed_subset isClosed_closure ((closure_mono hsub).trans
      closure_union.le)
  smul_mem' := by
    intro r s hs
    have hsub : germSupport k F (r • s) ⊆ germSupport k F s := by
      intro x hx hsx
      exact hx (by simp [map_smul, hsx])
    exact hs.of_isClosed_subset isClosed_closure (closure_mono hsub)

def compactSectionsMap {F G : CoefficientSheaf k Z} (a : F ⟶ G) :
    compactSections k F →ₗ[k] compactSections k G where
  toFun s := ⟨a.hom.app (op ⊤) s.1, by
    have hsub : germSupport k G (a.hom.app (op ⊤) s.1) ⊆ germSupport k F s.1 := by
      intro x hx hsx
      apply hx
      rw [← Presheaf.stalkFunctor_map_germ_apply, hsx]
      exact ((Presheaf.stalkFunctor (ModuleCat k) x).map a.hom).hom.map_zero
    exact s.2.of_isClosed_subset isClosed_closure (closure_mono hsub)⟩
  map_add' s t := by ext; exact map_add _ _ _
  map_smul' r s := by ext; exact map_smul _ _ _

def sections (Z : TopCat.{0}) : CoefficientSheaf k Z ⥤ ModuleCat.{0} k where
  obj F := ModuleCat.of k (compactSections k F)
  map a := ModuleCat.ofHom (compactSectionsMap k a)
  map_id _F := by ext s; rfl
  map_comp _a _b := by ext s; rfl

instance sectionsAdditive (Z : TopCat.{0}) : (sections k Z).Additive where
  map_add := by intro F G a b; ext s; rfl

instance sectionsLinear (Z : TopCat.{0}) : Functor.Linear k (sections k Z) where
  map_smul _a _r := by ext s; rfl

abbrev derivedSections (Z : TopCat.{0}) :
    DerivedCategory.Plus (CoefficientSheaf k Z) ⥤ DerivedCategory (ModuleCat.{0} k) :=
  (sections k Z).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι

abbrev vectorUnit : DerivedCategory (ModuleCat.{0} k) :=
  (DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)

abbrev unitPlus (Z : TopCat.{0}) : DerivedCategory.Plus (CoefficientSheaf k Z) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj ((constant k Z).obj (ModuleCat.of k k))

/-- The universal property refers to this actual compact-support derived functor. -/
structure DualizingComplex (Z : TopCat.{0}) where
  obj : CoefficientDerived k Z
  representation : DerivedCategory.Plus.ι.op ⋙ (linearYoneda k (CoefficientDerived k Z)).obj obj ≅
    (derivedSections k Z).op ⋙ (linearYoneda k (DerivedCategory (ModuleCat.{0} k))).obj (vectorUnit
      k)

/-- The compact-support trace uses the same selected native purity and representation. -/
def topTrace (Z : TopCat.{0}) (D : DualizingComplex k Z) (d : ℕ)
    (e : D.obj ≅ (coefficientUnit k Z)⟦(2*d : ℤ)⟧) :
    (derivedSections k Z).obj ((unitPlus k Z)⟦(2*d : ℤ)⟧) ⟶ vectorUnit k :=
  (D.representation.hom.app (op ((unitPlus k Z)⟦(2*d : ℤ)⟧))).hom
    ((DerivedCategory.Plus.ι.commShiftIso (2*d : ℤ)).hom.app (unitPlus k Z) ≫ e.inv)

end MathlibExt.AlgebraicGeometry.CoefficientCompactSupportModels
