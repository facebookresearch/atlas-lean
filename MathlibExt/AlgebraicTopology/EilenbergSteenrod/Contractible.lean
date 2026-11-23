/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractible-space consequences of the Eilenberg–Steenrod axioms

Absolute homology of a contractible space and the ordinary-theory dimension
consequence, derived from abstract homotopy invariance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TopPair.HomologyPretheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type*} {c : ComplexShape ι}

/-- A contractible space has the same absolute homology as a point for every
homotopy-invariant pretheory. -/
noncomputable def absoluteIsoOfContractible
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (X : Type w) [TopologicalSpace X] [ContractibleSpace X] (i : ι) :
    (E.H i).obj (TopCat.of X) ≅ (E.H i).obj (TopCat.of PUnit.{w + 1}) :=
  E.absoluteIsoOfHomotopyEquiv
    (Classical.choice (ContractibleSpace.hequiv (X := X) (Y := PUnit.{w + 1}))) i

lemma absoluteIsoOfContractible_hom_naturality
    {E F : HomologyPretheory.{w} C c} [E.IsHomotopyInvariant]
    [F.IsHomotopyInvariant] (α : E ⟶ F)
    (X : Type w) [TopologicalSpace X] [ContractibleSpace X] (i : ι) :
    (α.hom i).app (TopCat.of X) ≫ (F.absoluteIsoOfContractible X i).hom =
      (E.absoluteIsoOfContractible X i).hom ≫
        (α.hom i).app (TopCat.of PUnit.{w + 1}) := by
  exact E.absoluteIsoOfHomotopyEquiv_hom_naturality α
    (Classical.choice (ContractibleSpace.hequiv (X := X) (Y := PUnit.{w + 1}))) i

/-- The terminal map of a contractible space induces an isomorphism in every degree. -/
noncomputable instance isIso_map_isTerminalPUnit_from_of_contractible
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (X : TopCat.{w}) [ContractibleSpace X] (i : ι) :
    IsIso ((E.H i).map (TopCat.isTerminalPUnit.from X)) := by
  let e := E.absoluteIsoOfContractible ↑X i
  have h : e.hom = (E.H i).map (TopCat.isTerminalPUnit.from X) := by
    dsimp [e, absoluteIsoOfContractible]
    congr 1
  rw [← h]
  infer_instance

end TopPair.HomologyPretheory

namespace TopPair.GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A contractible space has the same absolute homology as a point for every
generalized homology theory. -/
noncomputable def absoluteIsoOfContractible
    (E : GeneralizedHomologyTheory.{u, v, w} C)
    (X : Type w) [TopologicalSpace X] [ContractibleSpace X] (n : ℤ) :
    (E.H n).obj (TopCat.of X) ≅
      (E.H n).obj (TopCat.of PUnit.{w + 1}) :=
  E.obj.absoluteIsoOfContractible X n

/-- Naturality of `absoluteIsoOfContractible` with respect to morphisms of
generalized homology theories. -/
lemma absoluteIsoOfContractible_hom_naturality
    {E F : GeneralizedHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (X : Type w) [TopologicalSpace X] [ContractibleSpace X] (n : ℤ) :
    (f.hom.hom n).app (TopCat.of X) ≫ (F.absoluteIsoOfContractible X n).hom =
      (E.absoluteIsoOfContractible X n).hom ≫
        (f.hom.hom n).app (TopCat.of PUnit.{w + 1}) :=
  HomologyPretheory.absoluteIsoOfContractible_hom_naturality f.hom X n

end TopPair.GeneralizedHomologyTheory

namespace TopPair.OrdinaryHomologyTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The homology of a contractible space is its coefficient object. -/
noncomputable def contractibleIsoCoefficientObject
    (E : OrdinaryHomologyTheory.{u, v, w} C)
    (X : Type w) [TopologicalSpace X] [ContractibleSpace X] (n : ℤ) :
    (E.H n).obj (TopCat.of X) ≅ E.obj.coefficientObject n :=
  E.obj.absoluteIsoOfContractible X n

/-- Naturality of `contractibleIsoCoefficientObject` with respect to morphisms
of ordinary homology theories. -/
lemma contractibleIsoCoefficientObject_hom_naturality
    {E F : OrdinaryHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (X : Type w) [TopologicalSpace X] [ContractibleSpace X] (n : ℤ) :
    (f.hom.hom n).app (TopCat.of X) ≫ (F.contractibleIsoCoefficientObject X n).hom =
      (E.contractibleIsoCoefficientObject X n).hom ≫
        (f.hom.hom n).app (TopCat.of PUnit.{w + 1}) :=
  GeneralizedHomologyTheory.absoluteIsoOfContractible_hom_naturality
    (OrdinaryHomologyTheory.forgetDimension.map f) X n

/-- An ordinary homology theory vanishes in nonzero degree on every
contractible space. -/
theorem isZero_of_contractible (E : OrdinaryHomologyTheory.{u, v, w} C)
    (n : ℤ) (hn : n ≠ 0) (X : Type w) [TopologicalSpace X]
    [ContractibleSpace X] : IsZero ((E.H n).obj (TopCat.of X)) :=
  (HomologyTheoryData.SatisfiesDimensionAxiom.isZero_point n hn).of_iso
    (E.contractibleIsoCoefficientObject X n)

end TopPair.OrdinaryHomologyTheory
