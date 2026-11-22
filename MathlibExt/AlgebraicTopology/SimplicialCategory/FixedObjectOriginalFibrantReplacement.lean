/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCodiscreteTerminal
import MathlibExt.CategoryTheory.SmallObject.FactorizationAccessibility

/-!
# The actual original horn replacement into the literal unit-Hom enrichment

The SAME native horn factorization of each original terminal map gives
a genuine full fixed-label fibrant replacement functor. Its whole unit,
right factor, naturality and exact factorization remain the actual
original native maps. Both finite original generator ends prove that
this SAME functor preserves filtered colimits. No weak terminal map or
desired interval is an input to the construction.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject
open scoped Simplicial
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalFibrantReplacement
variable (O : Type u)

/-- The actual complete original terminal natural transformation to the literal unit-Hom target. -/
def terminalMap : 𝟭 (FixedObjects O) ⟶ (Functor.const (FixedObjects O)).obj (CodiscreteTerminal.object O) where
  app := CodiscreteTerminal.toTerminal
  naturality _C _D f := (CodiscreteTerminal.toTerminal_naturality f).trans (Category.comp_id _).symm

/-- The SAME original terminal maps form the native whole Arrow functor. -/
abbrev inputFunctor : FixedObjects O ⥤ Arrow (FixedObjects O) := NatTrans.arrow (terminalMap O)

/-- The actual native horn replacement functor, with the SAME full object and Hom maps. -/
def functor : FixedObjects O ⥤ FixedObjects O := inputFunctor O ⋙ FreeFactorization.hornData.Z

/-- The original replacement object is literally the native horn middle object of its SAME terminal map. -/
theorem functor_obj (C : FixedObjects O) :
    (functor O).obj C = (FreeFactorization.horn (CodiscreteTerminal.toTerminal C)).Z := rfl

/-- The SAME whole native left factor gives the genuine original natural replacement unit. -/
def unit : 𝟭 (FixedObjects O) ⟶ functor O where
  app C := (FreeFactorization.horn (CodiscreteTerminal.toTerminal C)).i
  naturality _C _D f := FreeFactorization.hornData.i.naturality ((inputFunctor O).map f)

/-- The actual full original right factor retains the SAME literal terminal target. -/
def right (C : FixedObjects O) : (functor O).obj C ⟶ CodiscreteTerminal.object O :=
  (FreeFactorization.horn (CodiscreteTerminal.toTerminal C)).p

/-- Both original replacement factors recover the SAME whole original terminal map. -/
theorem factors (C : FixedObjects O) : (unit O).app C ≫ right O C = CodiscreteTerminal.toTerminal C :=
  FreeFactorization.horn_fac (CodiscreteTerminal.toTerminal C)

/-- The actual original right factor is the SAME full original terminal map of its native middle object. -/
theorem right_eq (C : FixedObjects O) : right O C = CodiscreteTerminal.toTerminal ((functor O).obj C) :=
  CodiscreteTerminal.toTerminal_unique _ _

/-- Every SAME whole original replacement unit is genuinely weak on all complete original Homs. -/
theorem unit_weak (C : FixedObjects O) : FixedObjectModel.weakEquivalences O ((unit O).app C) :=
  FixedObjectModel.trivialCofibrations_le_weakEquivalences _
    (FreeFactorization.horn (CodiscreteTerminal.toTerminal C)).hi

/-- The SAME complete original right factor is a genuine fibration in the original fixed-label model. -/
theorem right_fibration (C : FixedObjects O) : FixedObjectModel.fibrations O (right O C) :=
  (FreeFactorization.horn (CodiscreteTerminal.toTerminal C)).hp

/-- The SAME actual native replacement is fully fibrant in the original fixed-label model. -/
theorem object_isFibrant (C : FixedObjects O) :
    let _ : HomotopicalAlgebra.ModelCategory (FixedObjects O) := FixedObjectModel.modelCategory O
    HomotopicalAlgebra.IsFibrant ((functor O).obj C) := by
  let _ : HomotopicalAlgebra.ModelCategory (FixedObjects O) := FixedObjectModel.modelCategory O
  have hf : HomotopicalAlgebra.Fibration (right O C) :=
    (HomotopicalAlgebra.fibration_iff _).mpr (right_fibration O C)
  exact (HomotopicalAlgebra.isFibrant_iff_of_isTerminal (right O C)
    CodiscreteTerminal.isTerminal).mpr hf

/-- The SAME right factor detects weakness of the original terminal map through its actual native unit. -/
theorem right_weak_iff (C : FixedObjects O) :
    FixedObjectModel.weakEquivalences O (right O C) ↔
      FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal C) := by
  constructor
  · intro h
    have hc := (FixedObjectModel.weakEquivalences O).comp_mem _ _ (unit_weak O C) h
    exact (congrArg (fun f : C ⟶ CodiscreteTerminal.object O =>
      FixedObjectModel.weakEquivalences O f) (factors O C)).mp hc
  · intro h
    exact (FixedObjectModel.weakEquivalences O).of_precomp _ _ (unit_weak O C)
      ((congrArg (fun f : C ⟶ CodiscreteTerminal.object O =>
        FixedObjectModel.weakEquivalences O f) (factors O C)).mpr h)

/-- The original free-boundary lifting class detects the SAME terminal-map weakness after its native horn
replacement. -/
theorem right_boundary_rlp_iff (C : FixedObjects O) :
    (boundaryFamily O).rlp (right O C) ↔
      FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal C) := by
  change FixedObjectModel.trivialFibrations O (right O C) ↔ _
  rw [FixedObjectModel.trivialFibrations_eq]
  change (FixedObjectModel.fibrations O (right O C) ∧
    FixedObjectModel.weakEquivalences O (right O C)) ↔ _
  exact ⟨fun h => (right_weak_iff O C).mp h.2,
    fun h => ⟨right_fibration O C, (right_weak_iff O C).mpr h⟩⟩

/-- Both actual original horn generator ends are finitely presentable. -/
theorem horn_ends_presentable (i : (hornFamily O).toSet) :
    IsFinitelyPresentable.{u} i.val.left ∧ IsFinitelyPresentable.{u} i.val.right := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨n, x, y, k⟩⟩ := hf
  exact ⟨inferInstance, inferInstance⟩

/-- The SAME whole original native horn replacement preserves filtered colimits by its actual finite generator ends. -/
instance preservesFilteredColimits : (functor O).IsCardinalAccessible Cardinal.aleph0.{u} := by
  let _ : ∀ i : (hornFamily O).toSet, IsFinitelyPresentable.{u} i.val.left :=
    fun i => (horn_ends_presentable O i).1
  let _ : ∀ i : (hornFamily O).toSet, IsFinitelyPresentable.{u} i.val.right :=
    fun i => (horn_ends_presentable O i).2
  let _ : FreeFactorization.hornData.Z.IsCardinalAccessible Cardinal.aleph0.{u} :=
    SmallObject.functorialFactorizationData_Z_isCardinalAccessible
      (hornFamily O) Cardinal.aleph0.{u} Cardinal.aleph0.{u}
  let _ : (inputFunctor O).IsCardinalAccessible Cardinal.aleph0.{u} :=
    NatTrans.arrow_isCardinalAccessible (terminalMap O) Cardinal.aleph0.{u}
  dsimp only [functor]
  infer_instance

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalFibrantReplacement
