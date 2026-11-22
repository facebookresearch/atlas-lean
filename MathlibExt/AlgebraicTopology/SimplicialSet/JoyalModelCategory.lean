/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalModelCategory
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCategoricalEquivalences
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FibrantObjects

/-!
# The Joyal model structure

The categorical-equivalence class and the concrete finite-interval Smith input
construct the named model on `JoyalSSet`. Its cofibrations are monomorphisms,
its fibrations are genuine categorical fibrations, and its fibrant objects
are exactly quasicategories.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra
universe u
namespace JoyalSSet

private theorem categorical_fibrations_copy :
    SSet.categoricalFibrations.{u}.inverseImage forget.{u} =
      (monomorphisms JoyalSSet.{u} ⊓
        SSet.categoricalEquivalences.{u}.inverseImage forget.{u}).rlp := by
  have hMono : (monomorphisms SSet.{u}).inverseImage forget.{u} =
      monomorphisms JoyalSSet.{u} := by
    ext A B f
    change Mono (forget.map f) ↔ Mono f
    constructor
    · exact forget.mono_of_mono_map
    · intro hf
      let _ : Mono f := hf
      infer_instance
  calc
    SSet.categoricalFibrations.inverseImage forget =
        ((monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences).inverseImage
          equivalenceSSet.functor).rlp :=
      inverseImage_rlp_of_equivalence equivalenceSSet
        (monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences)
    _ = (monomorphisms JoyalSSet.{u} ⊓ SSet.categoricalEquivalences.inverseImage forget).rlp := by
      change ((monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences).inverseImage forget).rlp = _
      rw [MorphismProperty.inverseImage_inf, hMono]

/-- Proposed complete final witness; every datum is retained from the testing model. -/
theorem exists_joyal_modelCategory :
    let C := JoyalSSet.{u}
    let I : CategoryTheory.MorphismProperty C :=
      CategoryTheory.MorphismProperty.ofHoms
        (fun n : ℕ => JoyalSSet.ofSSet.{u}.map (SSet.boundary.{u} n).ι)
    let W : CategoryTheory.MorphismProperty C :=
      SSet.categoricalEquivalences.{u}.inverseImage JoyalSSet.forget.{u}
    let Monos := CategoryTheory.MorphismProperty.monomorphisms C
    let T := Monos ⊓ W
    let F := SSet.categoricalFibrations.{u}.inverseImage JoyalSSet.forget.{u}
    ∃ (s : HomotopicalAlgebra.SmithModelStructureData.{u} (C := C) I W)
      (M : HomotopicalAlgebra.ModelCategory C),
      letI : HomotopicalAlgebra.ModelCategory C := M
      let G := s.J
      ∃ κ : Cardinal.{u},
      ∃ regular : Fact κ.IsRegular,
      letI : Fact κ.IsRegular := regular
      ∃ bottom : OrderBot κ.ord.ToType,
      letI : OrderBot κ.ord.ToType := bottom
      ∃ cg : HomotopicalAlgebra.CofibrantGenerationData C κ,
        M.categoryWithCofibrations.cofibrations = Monos ∧
        M.categoryWithWeakEquivalences.weakEquivalences = W ∧
        M.categoryWithFibrations.fibrations = F ∧
        HomotopicalAlgebra.trivialCofibrations C = T ∧
        HomotopicalAlgebra.trivialFibrations C = I.rlp ∧
        I.rlp = Monos.rlp ∧
        F = T.rlp ∧
        F ⊓ W = I.rlp ∧
        CategoryTheory.MorphismProperty.IsWeakFactorizationSystem Monos I.rlp ∧
        CategoryTheory.MorphismProperty.IsWeakFactorizationSystem T F ∧
        G.rlp = F ∧
        G.rlp.llp = T ∧
        G ≤ T ∧
        I.IsSmall.{u} ∧ G.IsSmall.{u} ∧
        I.HasSmallObjectArgument.{u} ∧ G.HasSmallObjectArgument.{u} ∧
        CategoryTheory.IsCardinalLocallyPresentable C κ ∧
        I.IsCardinalForSmallObjectArgument κ ∧
        G.IsCardinalForSmallObjectArgument κ ∧
        cg.I = I ∧ cg.J = G ∧
        HomotopicalAlgebra.IsCombinatorialModelCategory.{u} C ∧
        (∀ X : C, HomotopicalAlgebra.IsFibrant X ↔
            SSet.Quasicategory (JoyalSSet.forget.obj X)) := by
  let C := JoyalSSet.{u}
  let I : MorphismProperty C :=
    .ofHoms (fun n : ℕ => ofSSet.{u}.map (SSet.boundary.{u} n).ι)
  let Wt : MorphismProperty C :=
    (SSet.joyalInterval.productPrecylinder.{u}.testingEquivalences
      SSet.joyalInterval.auxiliaryAnodyneExtensions.{u}).inverseImage forget.{u}
  let W : MorphismProperty C :=
    SSet.categoricalEquivalences.{u}.inverseImage forget.{u}
  let Monos := monomorphisms C
  let Tt := Monos ⊓ Wt
  let Ft := Tt.rlp
  let T := Monos ⊓ W
  let F := SSet.categoricalFibrations.{u}.inverseImage forget.{u}
  have hW : Wt = W :=
    congrArg (fun Q : MorphismProperty SSet.{u} => Q.inverseImage forget.{u})
      SSet.joyalInterval.testingEquivalences_eq_categoricalEquivalences.{u}
  have hF : F = T.rlp := categorical_fibrations_copy.{u}
  have hFt : Ft = F := by
    change (Monos ⊓ Wt).rlp = F
    rw [hW]
    exact hF.symm
  obtain ⟨s, M, witness⟩ := exists_finiteJoyalInterval_modelCategory.{u}
  let _ : ModelCategory C := M
  obtain ⟨κ, regular, witness⟩ := witness
  let _ : Fact κ.IsRegular := regular
  obtain ⟨bottom, witness⟩ := witness
  let _ : OrderBot κ.ord.ToType := bottom
  obtain ⟨cg, hMCof, hMW, hMF, hTC, hTF, hIrlp, hFW,
    hFirst, hSecond, hGRight, hGLeft, hGMem, hISmall, hGSmall,
    hISOA, hGSOA, hLP, hIκ, hGκ, hcgI, hcgJ, hComb⟩ := witness
  change M.categoryWithWeakEquivalences.weakEquivalences = Wt at hMW
  change M.categoryWithFibrations.fibrations = Ft at hMF
  change trivialCofibrations C = Tt at hTC
  change Ft ⊓ Wt = I.rlp at hFW
  change IsWeakFactorizationSystem Tt Ft at hSecond
  change s.J.rlp = Ft at hGRight
  change s.J.rlp.llp = Tt at hGLeft
  change s.J ≤ Tt at hGMem
  have hT : Tt = T := congrArg (fun Q : MorphismProperty C => Monos ⊓ Q) hW
  let s' : SmithModelStructureData.{u} (C := C) I W := hW ▸ s
  have projection_preserved :
      ∀ (Q Q' : MorphismProperty C) (e : Q = Q')
        (d : SmithModelStructureData.{u} (C := C) I Q), (e ▸ d).J = d.J := by
    intro Q Q' e d
    cases e
    rfl
  have hJ : s'.J = s.J := projection_preserved Wt W hW s
  have hMWeak : M.categoryWithWeakEquivalences.weakEquivalences = W := by
    exact hMW.trans hW
  have hMFib : M.categoryWithFibrations.fibrations = F := by
    exact hMF.trans hFt
  have hTC' : trivialCofibrations C = T := by
    exact hTC.trans hT
  have hFW' : F ⊓ W = I.rlp := by
    simpa only [hFt, hW] using hFW
  have hSecond' : IsWeakFactorizationSystem T F := by
    simpa only [hT, hFt] using hSecond
  have hGRight' : s'.J.rlp = F := by
    simpa only [hJ, hFt] using hGRight
  have hGLeft' : s'.J.rlp.llp = T := by
    simpa only [hJ, hT] using hGLeft
  have hGMem' : s'.J ≤ T := by
    simpa only [hJ, hT] using hGMem
  have hGSmall' : s'.J.IsSmall.{u} := by simpa only [hJ] using hGSmall
  have hGSOA' : s'.J.HasSmallObjectArgument.{u} := by simpa only [hJ] using hGSOA
  have hGκ' : s'.J.IsCardinalForSmallObjectArgument κ := by
    simpa only [hJ] using hGκ
  have hcgJ' : cg.J = s'.J := by simpa only [hJ] using hcgJ
  have fibrant_objects : ∀ X : C, IsFibrant X ↔ SSet.Quasicategory (forget.obj X) := by
    intro X
    let terminalRaw := terminal SSet.{u}
    let terminalCopy := ofSSet.obj terminalRaw
    let t : IsTerminal terminalCopy :=
        IsTerminal.isTerminalObj ofSSet (terminal SSet.{u}) terminalIsTerminal
    let p : X ⟶ terminalCopy := InducedCategory.homMk (terminal.from X.toSSet)
    let _ : (fibrations C).RespectsIso := by
      change M.categoryWithFibrations.fibrations.RespectsIso
      rw [hMFib]
      infer_instance
    rw [isFibrant_iff_of_isTerminal p t, fibration_iff]
    change M.categoryWithFibrations.fibrations p ↔ _
    rw [hMFib]
    change SSet.categoricalFibrations (terminal.from X.toSSet) ↔ _
    exact SSet.categoricalFibrations.terminalFrom_iff_quasicategory X.toSSet
  refine ⟨s', M, ?_⟩
  let _ : ModelCategory C := M
  refine ⟨κ, regular, ?_⟩
  let _ : Fact κ.IsRegular := regular
  refine ⟨bottom, ?_⟩
  let _ : OrderBot κ.ord.ToType := bottom
  exact ⟨cg, hMCof, hMWeak, hMFib, hTC', hTF, hIrlp, hF,
    hFW', hFirst, hSecond', hGRight', hGLeft', hGMem', hISmall,
    hGSmall', hISOA, hGSOA', hLP, hIκ, hGκ', hcgI, hcgJ', hComb,
    fibrant_objects⟩

/-- The selected Joyal model structure on the designated copy of simplicial sets. -/
@[instance_reducible]
noncomputable def modelCategory : ModelCategory JoyalSSet.{u} :=
  exists_joyal_modelCategory.{u}.choose_spec.choose

private theorem modelCategory_classifying_properties :
    modelCategory.{u}.categoryWithCofibrations.cofibrations =
        monomorphisms JoyalSSet.{u} ∧
      modelCategory.{u}.categoryWithWeakEquivalences.weakEquivalences =
        SSet.categoricalEquivalences.{u}.inverseImage forget.{u} ∧
      modelCategory.{u}.categoryWithFibrations.fibrations =
        SSet.categoricalFibrations.{u}.inverseImage forget.{u} := by
  let _ : ModelCategory JoyalSSet.{u} := modelCategory
  obtain ⟨κ, regular, h⟩ :=
    exists_joyal_modelCategory.{u}.choose_spec.choose_spec
  let _ : Fact κ.IsRegular := regular
  obtain ⟨bottom, h⟩ := h
  let _ : OrderBot κ.ord.ToType := bottom
  obtain ⟨_, hC, hW, hF, _⟩ := h
  exact ⟨hC, hW, hF⟩

/-- Cofibrations in the selected Joyal model structure are the monomorphisms. -/
theorem modelCategory_cofibrations :
    modelCategory.{u}.categoryWithCofibrations.cofibrations =
      monomorphisms JoyalSSet.{u} :=
  modelCategory_classifying_properties.{u}.1

/-- Fibrations in the selected Joyal model structure are the categorical fibrations. -/
theorem modelCategory_fibrations :
    modelCategory.{u}.categoryWithFibrations.fibrations =
      SSet.categoricalFibrations.{u}.inverseImage forget.{u} :=
  modelCategory_classifying_properties.{u}.2.2

/-- Weak equivalences in the selected Joyal model structure are the categorical equivalences. -/
theorem modelCategory_weakEquivalences :
    modelCategory.{u}.categoryWithWeakEquivalences.weakEquivalences =
      SSet.categoricalEquivalences.{u}.inverseImage forget.{u} :=
  modelCategory_classifying_properties.{u}.2.1

/-- Fibrant objects of the selected Joyal model are exactly the quasicategories
on their original simplicial-set carriers. -/
theorem isFibrant_iff_quasicategory (X : JoyalSSet.{u}) :
    let _ : ModelCategory JoyalSSet.{u} := modelCategory
    IsFibrant X ↔ SSet.Quasicategory X.toSSet := by
  let _ : ModelCategory JoyalSSet.{u} := modelCategory
  obtain ⟨κ, regular, h⟩ := exists_joyal_modelCategory.{u}.choose_spec.choose_spec
  let _ : Fact κ.IsRegular := regular
  obtain ⟨bottom, h⟩ := h
  let _ : OrderBot κ.ord.ToType := bottom
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hFibrant⟩ := h
  exact hFibrant X

/-- Combinatoriality of the selected scalar model uses its same original
common-cardinal witness and generating families. -/
theorem modelCategory_isCombinatorial :
    letI : ModelCategory JoyalSSet.{u} := modelCategory
    IsCombinatorialModelCategory.{u} JoyalSSet.{u} := by
  let _ : ModelCategory JoyalSSet.{u} := modelCategory
  obtain ⟨κ, regular, h⟩ := exists_joyal_modelCategory.{u}.choose_spec.choose_spec
  let _ : Fact κ.IsRegular := regular
  obtain ⟨bottom, h⟩ := h
  let _ : OrderBot κ.ord.ToType := bottom
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCombinatorial, _⟩ := h
  exact hCombinatorial

namespace ModelCategory

/-- Opt-in Joyal model-category instance on the designated copy of simplicial sets. -/
noncomputable scoped instance instModelCategory :
    HomotopicalAlgebra.ModelCategory JoyalSSet.{u} :=
  JoyalSSet.modelCategory

/-- Opt-in combinatoriality belongs to that same selected scalar model. -/
scoped instance instIsCombinatorialModelCategory :
    letI : HomotopicalAlgebra.ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    IsCombinatorialModelCategory.{u} JoyalSSet.{u} :=
  modelCategory_isCombinatorial

end ModelCategory

end JoyalSSet
