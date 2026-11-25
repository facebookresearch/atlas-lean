/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenRightHomotopyMap
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.RightHomotopyCofibrantYonedaWeak
import MathlibExt.AlgebraicTopology.ModelCategory.RightHomotopyClassWeakPostcomp

/-!
# Genuine Quillen recognition from actual model cores

The original right-class maps on bifibrant objects and actual weak object
coverage give the original Quillen criterion. The proof factors each
original adjoint map, transposes its actual trivial cofibration, and uses
genuine model class recognition. It does not accept a unit, counit or
derived-adjunction comparison as an input. This is the ordinary model
part of HTT A.3.1.10; higher mapping and object descent remain separate.
-/

noncomputable section
universe u₁ u₂ v₁ v₂
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- Actual right-class full faithfulness and genuine weak object coverage detect the SAME Quillen
equivalence when all
source objects are cofibrant and fibrant weakness is reflected. -/
theorem isQuillenEquivalence_of_coreRightClasses
    [IsQuillenAdjunction adj]
    (hC : ∀ X : C, IsCofibrant X)
    (hReflect : ∀ {F G : D} [IsFibrant F] [IsFibrant G] (f : F ⟶ G),
      WeakEquivalence (R.map f) → WeakEquivalence f)
    (hFull : ∀ (F G : D) [IsCofibrant F] [IsFibrant F] [IsCofibrant G] [IsFibrant G],
      Function.Bijective (IsQuillenAdjunction.rightHomotopyClassMap (adj := adj) (F := F) (G := G)))
    (hObjects : ∀ (Z : C) [IsFibrant Z], ∃ (G : D), IsCofibrant G ∧ IsFibrant G ∧
      ∃ g : Z ⟶ R.obj G, WeakEquivalence g) : IsQuillenEquivalence adj where
  homEquiv_weakEquivalence_iff {X Y} _ _ f := by
    let _ : IsCofibrant (L.obj X) := IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)
        inferInstance
    let d := MorphismProperty.factorizationData (trivialCofibrations D) (fibrations D) f
    let _ : Cofibration d.i := (cofibration_iff _).mpr d.hi.1
    let _ : WeakEquivalence d.i := (weakEquivalence_iff _).mpr d.hi.2
    let _ : Fibration d.p := (fibration_iff _).mpr d.hp
    let _ : IsCofibrant d.Z := isCofibrant_of_cofibration d.i
    let _ : IsFibrant d.Z := isFibrant_of_fibration d.p
    let _ : IsCofibrant (R.obj d.Z) := hC _
    let _ : IsFibrant (R.obj d.Z) := IsQuillenAdjunction.preservesFibrantObjects (adj := adj)
        inferInstance
    let g' : X ⟶ R.obj d.Z := adj.homEquiv X d.Z d.i
    have hpreImage (G : D) [IsCofibrant G] [IsFibrant G] :
        Function.Bijective (fun a : RightHomotopyClass (R.obj d.Z) (R.obj G) => a.precomp g') := by
      have hb := (IsQuillenAdjunction.rightHomotopyHomEquiv (adj := adj) X G).bijective.comp
        (RightHomotopyClass.precomp_bijective_of_weakEquivalence G d.i)
      have hc : Function.Bijective
          ((fun a : RightHomotopyClass (R.obj d.Z) (R.obj G) => a.precomp g') ∘
            IsQuillenAdjunction.rightHomotopyClassMap (adj := adj)) := by
        convert hb using 1
        funext a
        exact IsQuillenAdjunction.rightHomotopyClassMap_pre_homEquiv X d.i a
      exact ((hFull d.Z G).of_comp_iff _).mp hc
    have hpre (Z : C) [IsFibrant Z] :
        Function.Bijective (fun a : RightHomotopyClass (R.obj d.Z) Z => a.precomp g') := by
      obtain ⟨G, hGcof, hGfib, z, hz⟩ := hObjects Z
      let _ : IsCofibrant G := hGcof
      let _ : IsFibrant G := hGfib
      let _ : IsFibrant (R.obj G) := IsQuillenAdjunction.preservesFibrantObjects (adj := adj) hGfib
      let _ : WeakEquivalence z := hz
      have hb := (hpreImage G).comp
        (RightHomotopyClass.postcompOfCofibrant_bijective_of_weakEquivalence (X := R.obj d.Z) z)
      have hc : Function.Bijective
          ((fun a : RightHomotopyClass X Z => a.postcompOfCofibrant z) ∘
            (fun a : RightHomotopyClass (R.obj d.Z) Z => a.precomp g')) := by
        convert hb using 1
        funext a
        induction a using Quot.inductionOn with
        | _ a => exact congrArg RightHomotopyClass.mk (Category.assoc g' a z)
      exact hc.of_comp_left
        (RightHomotopyClass.postcompOfCofibrant_bijective_of_weakEquivalence (X := X) z).injective
    let _ : WeakEquivalence g' :=
      (weakEquivalence_iff_rightHomotopyClass_precomp_bijective_of_cofibrant g').mpr hpre
    have hf : WeakEquivalence f ↔ WeakEquivalence d.p := by
      simpa only [d.fac] using weakEquivalence_precomp_iff d.i d.p
    have hg : WeakEquivalence (adj.homEquiv X Y f) ↔ WeakEquivalence (R.map d.p) := by
      have he : adj.homEquiv X Y f = g' ≫ R.map d.p :=
        (congrArg (adj.homEquiv X Y) d.fac.symm).trans (adj.homEquiv_naturality_right d.i d.p)
      rw [he]
      exact weakEquivalence_precomp_iff g' (R.map d.p)
    have hp : WeakEquivalence (R.map d.p) ↔ WeakEquivalence d.p :=
      ⟨hReflect d.p, fun h => by
        let _ : WeakEquivalence d.p := h
        exact IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) d.p⟩
    simpa only [weakEquivalence_iff] using hf.trans (hp.symm.trans hg.symm)

/-- A genuine Quillen equivalence supplies actual bifibrant weak object representatives, with the
original transpose of
the original terminal factorization. -/
theorem exists_bifibrant_weak_hom_of_isQuillenEquivalence [IsQuillenEquivalence adj]
    (X : C) [IsCofibrant X] :
    ∃ (G : D), IsCofibrant G ∧ IsFibrant G ∧ ∃ g : X ⟶ R.obj G, WeakEquivalence g := by
  let _ : IsCofibrant (L.obj X) := IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)
      inferInstance
  let d := MorphismProperty.factorizationData (trivialCofibrations D) (fibrations D)
      (terminal.from (L.obj X))
  let _ : Cofibration d.i := (cofibration_iff _).mpr d.hi.1
  let _ : WeakEquivalence d.i := (weakEquivalence_iff _).mpr d.hi.2
  let _ : Fibration d.p := (fibration_iff _).mpr d.hp
  let _ : IsCofibrant d.Z := isCofibrant_of_cofibration d.i
  let _ : IsFibrant d.Z := (isFibrant_iff_of_isTerminal d.p terminalIsTerminal).mpr inferInstance
  exact ⟨d.Z, inferInstance, inferInstance, adj.homEquiv X d.Z d.i,
    (IsQuillenEquivalence.weakEquivalence_homEquiv_iff (adj := adj) d.i).mp inferInstance⟩

/-- A genuine Quillen equivalence makes the SAME original right-class maps bijective on bifibrant
objects when its right
image of the source is cofibrant. -/
theorem coreRightClasses_bijective_of_isQuillenEquivalence [IsQuillenEquivalence adj]
    (F G : D) [IsCofibrant F] [IsFibrant F] [IsFibrant G] [IsCofibrant (R.obj F)] :
    Function.Bijective (IsQuillenAdjunction.rightHomotopyClassMap (adj := adj) (F := F) (G := G))
        := by
  let _ : IsCofibrant (L.obj (R.obj F)) := IsQuillenAdjunction.preservesCofibrantObjects
      (adj := adj) inferInstance
  let ε : L.obj (R.obj F) ⟶ F := adj.counit.app F
  let _ : WeakEquivalence ε := IsQuillenEquivalence.weakEquivalence_counit F
  have hb : Function.Bijective (fun a : RightHomotopyClass F G =>
      IsQuillenAdjunction.rightHomotopyHomEquiv (adj := adj) (R.obj F) G (a.precomp ε)) :=
    (IsQuillenAdjunction.rightHomotopyHomEquiv (adj := adj) (R.obj F) G).bijective.comp
      (RightHomotopyClass.precomp_bijective_of_weakEquivalence G ε)
  have hε : adj.homEquiv (R.obj F) F ε = 𝟙 (R.obj F) := by
    apply (adj.homEquiv (R.obj F) F).symm.injective
    simp [ε, Adjunction.homEquiv_counit]
  convert hb using 1
  funext a
  induction a using Quot.inductionOn with
  | _ a =>
    change RightHomotopyClass.mk (R.map a) =
      RightHomotopyClass.mk (adj.homEquiv (R.obj F) G (ε ≫ a))
    exact congrArg RightHomotopyClass.mk
        (by rw [adj.homEquiv_naturality_right, hε, Category.id_comp])

end CategoryTheory.Adjunction
