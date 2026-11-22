/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalRowFibrations
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSet.SegalOuterHornCFiltration

/-!
# The original auxiliary C to U mapping restriction
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen SimplicialSpace.Inner

namespace SimplicialSpace.OuterHornCMapping

/-- The prescribed original U to C inclusion, retaining its ambient subcomplexes. -/
def inclusion (m : ℕ) :
    (SSet.Rezk.outerHornCU.{u} m : SSet.{u}) ⟶
      (SSet.Rezk.outerHornC (m + 2) : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (SSet.Rezk.outerHornCU_le_C m)

/-- Restriction of the actual inner mapping end along the original inclusion. -/
def restriction (W : SimplicialSpace.{u}) (m : ℕ) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.outerHornC (m + 2) : SSet.{u})) ⟶
      (discreteSourceMapping W).obj (op (SSet.Rezk.outerHornCU m : SSet.{u})) :=
  (discreteSourceMapping W).map (inclusion m).op

/-- The same inclusion factors through the original ambient simplex inclusion. -/
@[reassoc]
theorem inclusion_ambient (m : ℕ) :
    inclusion.{u} m ≫ (SSet.Rezk.outerHornC (m + 2)).ι =
      (SSet.Rezk.outerHornCU m).ι := rfl

/-- The original inclusion has its actual finite inner-horn filtration. -/
theorem inclusion_innerAnodyne (m : ℕ) : SSet.innerAnodyneExtensions (inclusion.{u} m) :=
  SSet.Rezk.outerHornCU_to_C_innerAnodyne m

/-- Every original boundary square for the same restriction has a lift. -/
theorem restriction_boundaryRLP (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    SSet.modelCategoryQuillen.I.rlp (restriction W m) := by
  have hSpine : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
      ((boxLeftDivisionFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app W) := by
    intro n hn
    exact hW.2 n hn
  exact leftRestriction_boundaryRLP_of_innerAnodyne W hW.1 hSpine
    (inclusion m) (inclusion_innerAnodyne m)

/-- The actual scalar restriction is a genuine Kan trivial fibration. -/
theorem restriction_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    trivialFibrations SSet.{u} (restriction W m) := by
  rw [← cofibrations_rlp]
  change (monomorphisms SSet.{u}).rlp (restriction W m)
  rw [SSet.rlp_monomorphisms]
  exact restriction_boundaryRLP W hW m

/-- The same original map induces all realization homotopy-group equivalences. -/
theorem restriction_realizationWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    SSet.realizationWeakEquivalences (restriction W m) :=
  (restriction_trivialFibration W hW m).2

/-- The designated original C mapping object is Kan from actual source cofibrancy. -/
theorem mappingC_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    SSet.KanComplex
      ((discreteSourceMapping W).obj (op (SSet.Rezk.outerHornC (m + 2) : SSet.{u}))) :=
  ReedyModel.innerHom_kanComplex
    (discreteInnerFunctor.obj (SSet.Rezk.outerHornC (m + 2) : SSet.{u})) W
    (ReedyModel.isCofibrant _) hW.1

/-- The designated original U mapping object is Kan from the same actual cofibrancy supplier. -/
theorem mappingU_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    SSet.KanComplex
      ((discreteSourceMapping W).obj (op (SSet.Rezk.outerHornCU m : SSet.{u}))) :=
  ReedyModel.innerHom_kanComplex
    (discreteInnerFunctor.obj (SSet.Rezk.outerHornCU m : SSet.{u})) W
    (ReedyModel.isCofibrant _) hW.1

/-- The original restriction induces the full native Kan fundamental-groupoid and based π
equivalences. -/
theorem restriction_KanComplexW (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    SSet.KanComplex.W (restriction W m) := by
  let _ := mappingC_kan W hW m
  let _ := mappingU_kan W hW m
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence (restriction W m)).mpr
    (restriction_realizationWeak W hW m)

/-- Arbitrary target maps preserve the same restriction and all original operators. -/
@[reassoc]
theorem restriction_naturality {W V : SimplicialSpace.{u}} (q : W ⟶ V) (m : ℕ) :
    (discreteSourceMappingMap q).app
        (op (SSet.Rezk.outerHornC (m + 2) : SSet.{u})) ≫ restriction V m =
      restriction W m ≫ (discreteSourceMappingMap q).app
        (op (SSet.Rezk.outerHornCU m : SSet.{u})) :=
  ((discreteSourceMappingMap q).naturality (inclusion m).op).symm

/-- Mapping the ambient factor keeps the entire original contravariant composite. -/
@[reassoc]
theorem restriction_ambient (W : SimplicialSpace.{u}) (m : ℕ) :
    (discreteSourceMapping W).map (SSet.Rezk.outerHornC (m + 2)).ι.op ≫ restriction W m =
      (discreteSourceMapping W).map (SSet.Rezk.outerHornCU m).ι.op := by
  dsimp only [restriction]
  rw [← (discreteSourceMapping W).map_comp, ← op_comp, inclusion_ambient]

/-- At the first index the prescribed U and C are the same original edge01. -/
theorem inclusion_zero_isIso : IsIso (inclusion.{u} 0) := by
  have h : SSet.Rezk.outerHornCU.{u} 0 = SSet.Rezk.outerHornC 2 := by
    rw [SSet.Rezk.outerHornCU_zero, SSet.Rezk.outerHornC_two]
  let e := SSet.Subcomplex.eqToIso h
  have he : inclusion.{u} 0 = e.hom := by
    apply (cancel_mono (SSet.Rezk.outerHornC.{u} 2).ι).1
    rw [inclusion_ambient]
    exact (SSet.Subcomplex.homOfLE_ι h.le).symm
  rw [he]
  infer_instance

/-- The same initial restriction is an actual isomorphism for every raw target. -/
theorem restriction_zero_isIso (W : SimplicialSpace.{u}) : IsIso (restriction W 0) := by
  let _ := inclusion_zero_isIso.{u}
  dsimp only [restriction]
  infer_instance

end SimplicialSpace.OuterHornCMapping
