/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PointedRightMappingTrivialFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations
public import MathlibExt.AlgebraicTopology.ModelCategory.Under
public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantBrown

/-!
# Unconditional same-map right-mapping weakness by Brown's lemma

The actual two-pointed Joyal carrier is a genuine under model category.
Its right mapping functor preserves true trivial fibrations by original
boundary lifting. Brown's lemma therefore preserves weak maps between
its fibrant objects. The pointed/unwrapped arrow isomorphism gives the
same original right mapping-space map, without a simplex-full-faithfulness
certificate or cofibrancy assumption on the pointed source.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.JoyalRightMapping

attribute [local instance] JoyalSSet.modelCategory modelCategoryQuillen.modelCategory

/-- The literal two original vertices, on the actual designated Joyal carrier. -/
def endpointObject : JoyalSSet.{u} :=
  JoyalSSet.ofSSet.obj PointedRightMappingSpace.endpointPair

/-- Forget only the Joyal carrier tag of the same actually pointed original object. -/
def forgetPointed : Under endpointObject.{u} ⥤ Under PointedRightMappingSpace.endpointPair.{u} where
  obj P := Under.mk (JoyalSSet.forget.map P.hom)
  map f := Under.homMk (JoyalSSet.forget.map f.right) (by
    exact (JoyalSSet.forget.map_comp _ _).symm.trans
      (congrArg (fun g => JoyalSSet.forget.map g) (Under.w f)))
  map_id P := by
    apply StructuredArrow.hom_ext
    exact JoyalSSet.forget.map_id P.right
  map_comp f g := by
    apply StructuredArrow.hom_ext
    exact JoyalSSet.forget.map_comp f.right g.right

/-- The actual same-endpoint right mapping-space functor from the genuine two-pointed Joyal category. -/
def functor : Under endpointObject.{u} ⥤ SSet.{u} :=
  forgetPointed ⋙ PointedRightMappingSpace.functor

private theorem raw_trivialFibration {P Q : JoyalSSet.{u}} (p : P ⟶ Q)
    (hp : trivialFibrations JoyalSSet.{u} p) :
    modelCategoryQuillen.I.rlp (JoyalSSet.forget.map p) := by
  obtain ⟨hF, hW⟩ := (mem_trivialFibrations_iff (f := p)).mp hp
  have hcatF : categoricalFibrations (JoyalSSet.forget.map p) := by
    have h := (fibration_iff p).mp hF
    change JoyalSSet.modelCategory.categoryWithFibrations.fibrations p at h
    rw [JoyalSSet.modelCategory_fibrations] at h
    exact h
  have hcatW : categoricalEquivalences (JoyalSSet.forget.map p) := by
    have h := (weakEquivalence_iff p).mp hW
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences p at h
    rw [JoyalSSet.modelCategory_weakEquivalences] at h
    exact h
  exact (categoricalFibrations_and_categoricalEquivalences_iff _).mp ⟨hcatF, hcatW⟩

/-- The genuine two-pointed Joyal functor preserves full original trivial fibrations into the actual
  Kan–Quillen model. -/
theorem map_trivialFibration {P Q : Under endpointObject.{u}} (p : P ⟶ Q)
    (hp : trivialFibrations (Under endpointObject.{u}) p) :
    trivialFibrations SSet.{u} (functor.map p) := by
  have hright : trivialFibrations JoyalSSet.{u} p.right := by
    have h := hp
    rw [trivialFibrations_under_eq, MorphismProperty.under_iff] at h
    exact h
  have hI : modelCategoryQuillen.I.rlp (functor.map p) :=
    PointedRightMappingSpace.map_mem_I_rlp (forgetPointed.map p) (raw_trivialFibration p.right hright)
  rw [← cofibrations_rlp]
  change (MorphismProperty.monomorphisms SSet.{u}).rlp (functor.map p)
  rw [rlp_monomorphisms]
  exact hI

private def terminalUnder {T : JoyalSSet.{u}} (hT : IsTerminal T) :
    IsTerminal (Under.mk (hT.from endpointObject.{u})) :=
  IsTerminal.ofUniqueHom
    (fun P => Under.homMk (hT.from P.right) (hT.hom_ext _ _))
    (fun P g => by
      apply StructuredArrow.hom_ext
      exact hT.hom_ext _ _)

/-- Original quasicategory fibrancy gives genuine fibrancy of its two-pointed object, including coincident endpoints. -/
theorem pointed_isFibrant (P : Under endpointObject.{u})
    (hP : Quasicategory P.right.toSSet) : IsFibrant P := by
  let T := JoyalSSet.ofSSet.obj (⊤_ SSet.{u})
  let hT : IsTerminal T := IsTerminal.isTerminalObj
    JoyalSSet.ofSSet (⊤_ SSet.{u}) terminalIsTerminal
  let q : P ⟶ Under.mk (hT.from endpointObject.{u}) :=
    Under.homMk (hT.from P.right) (hT.hom_ext _ _)
  have hraw : IsFibrant P.right := (JoyalSSet.isFibrant_iff_quasicategory P.right).mpr hP
  have hq : Fibration q := (fibrations_under_iff endpointObject q).mpr
    ((isFibrant_iff_of_isTerminal q.right hT).mp hraw)
  exact (isFibrant_iff_of_isTerminal q (terminalUnder hT)).mpr hq

/-- Brown's actual trivial-fibration factorization gives right-mapping weakness between the supplied
  two-pointed quasicategories. -/
theorem map_weak_of_categoricalEquivalence {P Q : Under endpointObject.{u}} (p : P ⟶ Q)
    (hP : Quasicategory P.right.toSSet) (hQ : Quasicategory Q.right.toSSet)
    (hp : categoricalEquivalences (JoyalSSet.forget.map p.right)) :
    realizationWeakEquivalences (functor.map p) := by
  let _ : IsFibrant P := pointed_isFibrant P hP
  let _ : IsFibrant Q := pointed_isFibrant Q hQ
  let _ : WeakEquivalence p.right := by
    rw [weakEquivalence_iff]
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences p.right
    rw [JoyalSSet.modelCategory_weakEquivalences]
    exact hp
  let _ : WeakEquivalence p := (weakEquivalences_under_iff endpointObject p).mpr inferInstance
  change weakEquivalences SSet.{u} (functor.map p)
  exact functor.map_mem_of_weakEquivalence_of_fibrant (weakEquivalences SSet.{u})
    (MorphismProperty.isomorphisms_le_of_containsIdentities (weakEquivalences SSet.{u}))
    (by
      intro A B p _ _ hp
      exact (map_trivialFibration p hp).2) p

/-- The actual two-pointed Joyal object carrying the supplied original vertex maps. -/
def of (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) : Under endpointObject.{u} :=
  Under.mk (JoyalSSet.ofSSet.map (coprod.desc x y))

/-- The supplied original map on that same two-pointed Joyal carrier. -/
def ofMap {X Y : SSet.{u}} (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    of X x y ⟶ of Y (x ≫ f) (y ≫ f) :=
  Under.homMk (JoyalSSet.ofSSet.map f) (by
    apply InducedCategory.hom_ext
    change coprod.desc x y ≫ f = coprod.desc (x ≫ f) (y ≫ f)
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, coprod.inr_desc])

end SSet.JoyalRightMapping

namespace SSet
open CategoryTheory HomotopicalAlgebra
variable {X Y : SSet.{u}}

/-- A genuine categorical equivalence between original quasicategories is weak on the actual same-map right
  mapping spaces, with no extra simplex-full-faithfulness hypothesis. -/
theorem categoricalEquivalences.rightMappingSpaceMap_weak {f : X ⟶ Y}
    [Quasicategory X] [Quasicategory Y] (hf : categoricalEquivalences f)
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    realizationWeakEquivalences (mappingSpaceRight.map X x y f) := by
  have h := JoyalRightMapping.map_weak_of_categoricalEquivalence (JoyalRightMapping.ofMap x y f)
    (show Quasicategory X from inferInstance) (show Quasicategory Y from inferInstance) hf
  change realizationWeakEquivalences
    (PointedRightMappingSpace.functor.map (PointedRightMappingSpace.ofMap x y f)) at h
  exact (realizationWeakEquivalences.arrow_mk_iso_iff
    (PointedRightMappingSpace.originalMapArrowIso x y f)).mp h

/-- The unconditional same-map categorical-to-Dwyer–Kan direction on the original quasicategories. -/
theorem categoricalEquivalences.isDwyerKanEquivalence {f : X ⟶ Y}
    [Quasicategory X] [Quasicategory Y] (hf : categoricalEquivalences f) :
    isDwyerKanEquivalence f :=
  ⟨hf.dwyerKanEssentiallySurjective, fun x y => hf.rightMappingSpaceMap_weak x y⟩

end SSet
