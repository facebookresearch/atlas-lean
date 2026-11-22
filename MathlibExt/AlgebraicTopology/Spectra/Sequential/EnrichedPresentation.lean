/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Evaluation
public import MathlibExt.AlgebraicTopology.Spectra.Sequential.EnrichedIndex
public import MathlibExt.CategoryTheory.Monoidal.TensorInitial
public import MathlibExt.CategoryTheory.Enriched.Evaluation
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda
public import MathlibExt.CategoryTheory.Enriched.FunctorMapCongruence
public import Mathlib.Data.Nat.Init

/-!
# Sequential spectra as enriched functors

The forward functor keeps the original levels and uses the original ordered
left iteration after the positive right-action braid. The inverse extracts the
K-left successor map through the degree-one isomorphism and the inverse braid.
Full Hom-object composition determines all higher actions from those successors.

The resulting equivalence uses genuine unit-graded transformations, retaining
full enriched naturality. Its free/evaluation comparison keeps the original
adjunction, unit, counit, generator arrows and degreewise free-object maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory Limits
open scoped MonoidalClosed ExternalProduct

namespace CategoryTheory.SequentialSpectrum.EnrichedPresentation

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasInitial C] {K : C}

attribute [local instance] EnrichedIndex.enrichedCategory

/-- The genuine enriched-functor category, with full unit-graded morphisms. -/
abbrev Carrier (K : C) := EnrichedFunctorCat C (EnrichedIndex.Index K)

/-- Right-oriented ordered action on the literal finite tensor power. -/
def orderedAction (X : SequentialSpectrum C K) (p n : ℕ) :
    X.level n ⊗ TensorPower.tensorPowObj K p ⟶ X.level (p + n) :=
  (β_ (X.level n) (TensorPower.tensorPowObj K p)).hom ≫ iteratedStructureMap X p n

omit [MonoidalClosed C] [HasInitial C] in
/-- Original ordered iteration and the positive reverse braid give full action composition. -/
theorem orderedAction_comp (X : SequentialSpectrum C K) (p q n : ℕ) :
    (X.level n ◁
      ((β_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q)).hom ≫
        (TensorPower.tensorPowObj_add K q p).inv ≫
        eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm q p)))) ≫
        orderedAction X (p + q) n ≫
        eqToHom (congrArg X.level (show (p + q) + n = q + (p + n) by omega)) =
      (α_ (X.level n) (TensorPower.tensorPowObj K p)
        (TensorPower.tensorPowObj K q)).inv ≫
        (orderedAction X p n ▷ TensorPower.tensorPowObj K q) ≫
        orderedAction X q (p + n) := by
  let A := X.level n
  let P := TensorPower.tensorPowObj K p
  let Q := TensorPower.tensorPowObj K q
  let μ := (TensorPower.tensorPowObj_add K q p).inv
  have hWord : ((β_ A P).hom ▷ Q) ≫ (β_ (P ⊗ A) Q).hom ≫ (α_ Q P A).inv =
      (α_ A P Q).hom ≫ (A ◁ (β_ P Q).hom) ≫ (β_ A (Q ⊗ P)).hom := by
    rw [braiding_tensor_left_hom, braiding_tensor_right_hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun f => (α_ A P Q).hom ≫ f ≫ (α_ Q P A).inv)
        (yang_baxter A P Q)
  have hPrefix : (α_ A P Q).inv ≫ ((β_ A P).hom ▷ Q) ≫
      (β_ (P ⊗ A) Q).hom =
        (A ◁ (β_ P Q).hom) ≫ (β_ A (Q ⊗ P)).hom ≫ (α_ Q P A).hom := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using
      congrArg (fun f => (α_ A P Q).inv ≫ f ≫ (α_ Q P A).hom) hWord
  have hDegree : (A ◁ eqToHom (congrArg (TensorPower.tensorPowObj K)
      (Nat.add_comm q p))) ≫ orderedAction X (p + q) n ≫
      eqToHom (congrArg X.level (show (p + q) + n = q + (p + n) by omega)) =
      orderedAction X (q + p) n ≫
      eqToHom (congrArg X.level (Nat.add_assoc q p n)) := by
    have h := eqToHom_naturality (fun m => orderedAction X m n) (Nat.add_comm q p)
    have hPost := congrArg (fun f => f ≫ eqToHom (congrArg X.level
      (show (p + q) + n = q + (p + n) by omega))) h.symm
    simpa only [A, whiskerLeft_eqToHom, Category.assoc, eqToHom_trans] using hPost
  have hPairing : (μ ▷ A) ≫ iteratedStructureMap X (q + p) n ≫
      eqToHom (congrArg X.level (Nat.add_assoc q p n)) =
      (α_ Q P A).hom ≫ (Q ◁ iteratedStructureMap X p n) ≫
        iteratedStructureMap X q (p + n) := by
    have hIdentity : TensorPower.laxTensorPowerPairing (𝟭 C) K q p = μ := by
      change 𝟙 _ ≫ (TensorPower.tensorPowObj_add K q p).inv = _
      exact Category.id_comp _
    simpa only [hIdentity, μ, A, P, Q, tensorHom_id, id_tensorHom] using
      iteratedStructureMap_add X q p n
  have hIterationBraid : (iteratedStructureMap X p n ▷ Q) ≫
      (β_ (X.level (p + n)) Q).hom =
      (β_ (P ⊗ A) Q).hom ≫ (Q ◁ iteratedStructureMap X p n) :=
    braiding_naturality_left (iteratedStructureMap X p n) Q
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hDegree]
  dsimp only [orderedAction]
  simp only [Category.assoc]
  rw [braiding_naturality_right_assoc]
  rw [hPairing]
  have hPrefixPost := congrArg
    (fun f : A ⊗ (P ⊗ Q) ⟶ Q ⊗ (P ⊗ A) =>
      f ≫ (Q ◁ iteratedStructureMap X p n) ≫ iteratedStructureMap X q (p + n)) hPrefix.symm
  have hIterationPost := congrArg
    (fun f : (P ⊗ A) ⊗ Q ⟶ Q ⊗ X.level (p + n) =>
      (α_ A P Q).inv ≫ ((β_ A P).hom ▷ Q) ≫ f ≫
        iteratedStructureMap X q (p + n)) hIterationBraid.symm
  simp only [Category.assoc] at hPrefixPost hIterationPost
  have hBoth := hPrefixPost.trans hIterationPost
  simpa only [A, P, Q, orderedAction, comp_whiskerRight, Category.assoc] using hBoth

/-- The actual right Hom action, obtained from the original ordered left iteration. -/
def spectrumAction (X : SequentialSpectrum C K) (a b : EnrichedIndex.Index K) :
    X.level a.degree ⊗ EnrichedIndex.indexHom K a b ⟶ X.level b.degree := by
  by_cases h : a.degree ≤ b.degree
  · exact eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z)
      (EnrichedIndex.indexHom_of_le K a b h)) ≫
      (β_ (X.level a.degree) (TensorPower.tensorPowObj K (b.degree - a.degree))).hom ≫
      iteratedStructureMap X (b.degree - a.degree) a.degree ≫
      eqToHom (congrArg X.level (Nat.sub_add_cancel h))
  · exact eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z)
      (EnrichedIndex.indexHom_of_gt K a b (Nat.lt_of_not_ge h))) ≫
      (MonoidalCategory.tensorInitialLeft (X.level a.degree)).to (X.level b.degree)

/-- Forward-degree actions retain the original iteration and its exact degree transport. -/
theorem spectrumAction_of_le (X : SequentialSpectrum C K) (a b : EnrichedIndex.Index K)
    (h : a.degree ≤ b.degree) :
    spectrumAction X a b =
      eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z)
        (EnrichedIndex.indexHom_of_le K a b h)) ≫
      (β_ (X.level a.degree) (TensorPower.tensorPowObj K (b.degree - a.degree))).hom ≫
      iteratedStructureMap X (b.degree - a.degree) a.degree ≫
      eqToHom (congrArg X.level (Nat.sub_add_cancel h)) := by
  simp only [spectrumAction, dite_eq_left h]

/-- Backward-degree actions are the actual initial maps on the full tensor domain. -/
theorem spectrumAction_of_gt (X : SequentialSpectrum C K) (a b : EnrichedIndex.Index K)
    (h : b.degree < a.degree) :
    spectrumAction X a b =
      eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z)
        (EnrichedIndex.indexHom_of_gt K a b h)) ≫
      (MonoidalCategory.tensorInitialLeft (X.level a.degree)).to (X.level b.degree) := by
  simp only [spectrumAction, dite_eq_right (Nat.not_le_of_gt h)]

/-- Original level maps commute with the entire Hom-object action, including backward degrees. -/
theorem spectrumAction_naturality {X Y : SequentialSpectrum C K} (f : X ⟶ Y)
    (a b : EnrichedIndex.Index K) :
    spectrumAction X a b ≫ f.levelMap b.degree =
      (f.levelMap a.degree ⊗ₘ 𝟙 (EnrichedIndex.indexHom K a b)) ≫ spectrumAction Y a b := by
  by_cases h : a.degree ≤ b.degree
  · let p := b.degree - a.degree
    let P := TensorPower.tensorPowObj K p
    let H := EnrichedIndex.indexHom K a b
    have hH : H = P := EnrichedIndex.indexHom_of_le K a b h
    have hDegree : p + a.degree = b.degree := Nat.sub_add_cancel h
    have hCast : (f.levelMap a.degree ⊗ₘ 𝟙 H) ≫
        eqToHom (congrArg (fun Z => Y.level a.degree ⊗ Z) hH) =
      eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z) hH) ≫
        (f.levelMap a.degree ⊗ₘ 𝟙 P) :=
      eqToHom_naturality (fun Z => f.levelMap a.degree ⊗ₘ 𝟙 Z) hH
    have hTarget : eqToHom (congrArg X.level hDegree) ≫ f.levelMap b.degree =
        f.levelMap (p + a.degree) ≫ eqToHom (congrArg Y.level hDegree) :=
      (eqToHom_naturality (fun n => f.levelMap n) hDegree).symm
    have hBraid : (f.levelMap a.degree ⊗ₘ 𝟙 P) ≫ (β_ (Y.level a.degree) P).hom =
        (β_ (X.level a.degree) P).hom ≫ (𝟙 P ⊗ₘ f.levelMap a.degree) := by
      simpa only [tensorHom_id, id_tensorHom] using
        braiding_naturality_left (f.levelMap a.degree) P
    have hIteration := iteratedStructureMap_naturality f p a.degree
    rw [spectrumAction_of_le X a b h, spectrumAction_of_le Y a b h]
    simp only [Category.assoc]
    change eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z) hH) ≫
        (β_ (X.level a.degree) P).hom ≫ iteratedStructureMap X p a.degree ≫
          eqToHom (congrArg X.level hDegree) ≫ f.levelMap b.degree =
      (f.levelMap a.degree ⊗ₘ 𝟙 H) ≫
        eqToHom (congrArg (fun Z => Y.level a.degree ⊗ Z) hH) ≫
        (β_ (Y.level a.degree) P).hom ≫ iteratedStructureMap Y p a.degree ≫
          eqToHom (congrArg Y.level hDegree)
    calc
      _ = eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z) hH) ≫
          (β_ (X.level a.degree) P).hom ≫ iteratedStructureMap X p a.degree ≫
          f.levelMap (p + a.degree) ≫ eqToHom (congrArg Y.level hDegree) := by
        simpa only [Category.assoc] using congrArg
          (fun m => eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z) hH) ≫
            (β_ (X.level a.degree) P).hom ≫ iteratedStructureMap X p a.degree ≫ m) hTarget
      _ = eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z) hH) ≫
          (β_ (X.level a.degree) P).hom ≫ (𝟙 P ⊗ₘ f.levelMap a.degree) ≫
          iteratedStructureMap Y p a.degree ≫ eqToHom (congrArg Y.level hDegree) := by
        simpa only [Category.assoc] using congrArg
          (fun m => eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z) hH) ≫
            (β_ (X.level a.degree) P).hom ≫ m ≫
              eqToHom (congrArg Y.level hDegree)) hIteration
      _ = eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z) hH) ≫
          (f.levelMap a.degree ⊗ₘ 𝟙 P) ≫ (β_ (Y.level a.degree) P).hom ≫
          iteratedStructureMap Y p a.degree ≫ eqToHom (congrArg Y.level hDegree) := by
        simpa only [Category.assoc] using congrArg
          (fun m => eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z) hH) ≫ m ≫
            iteratedStructureMap Y p a.degree ≫ eqToHom (congrArg Y.level hDegree))
          hBraid.symm
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun m => m ≫ (β_ (Y.level a.degree) P).hom ≫
            iteratedStructureMap Y p a.degree ≫ eqToHom (congrArg Y.level hDegree)) hCast.symm
  · have hInitial : IsInitial (X.level a.degree ⊗ EnrichedIndex.indexHom K a b) := by
      rw [EnrichedIndex.indexHom, ite_eq_right h]
      exact MonoidalCategory.tensorInitialLeft _
    exact hInitial.hom_ext _ _

omit [BraidedCategory C] [MonoidalClosed C] [HasInitial C] in
private theorem heqWhiskerLeft {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (hA : A = A') (hB : B = B') (hfg : f ≍ g)
    (X X' : C) (hX : X = X') : (X ◁ f) ≍ (X' ◁ g) := by
  cases hA
  cases hB
  cases hX
  cases eq_of_heq hfg
  rfl

omit [BraidedCategory C] [MonoidalClosed C] [HasInitial C] in
private theorem heqWhiskerRight {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (hA : A = A') (hB : B = B') (hfg : f ≍ g)
    (X X' : C) (hX : X = X') : (f ▷ X) ≍ (g ▷ X') := by
  cases hA
  cases hB
  cases hX
  cases eq_of_heq hfg
  rfl

omit [BraidedCategory C] [MonoidalClosed C] [HasInitial C] in
private theorem heqAssocInv (A B D A' B' D' : C)
    (hA : A = A') (hB : B = B') (hD : D = D') :
    (α_ A B D).inv ≍ (α_ A' B' D').inv := by
  cases hA
  cases hB
  cases hD
  rfl

omit [MonoidalClosed C] [HasInitial C] in
private theorem orderedAction_congr (X : SequentialSpectrum C K)
    (p n p' n' : ℕ) (hp : p = p') (hn : n = n') :
    orderedAction X p n ≍ orderedAction X p' n' := by
  cases hp
  cases hn
  rfl

/-- Forward actions have exactly the original ordered action under their endpoint transports. -/
theorem spectrumAction_heq_orderedAction (X : SequentialSpectrum C K)
    (a b : EnrichedIndex.Index K) (h : a.degree ≤ b.degree) :
    spectrumAction X a b ≍ orderedAction X (b.degree - a.degree) a.degree := by
  let m := orderedAction X (b.degree - a.degree) a.degree
  let e := eqToHom (congrArg (fun Z => X.level a.degree ⊗ Z)
    (EnrichedIndex.indexHom_of_le K a b h))
  let t := eqToHom (congrArg X.level (Nat.sub_add_cancel h))
  have hAction : spectrumAction X a b = e ≫ (m ≫ t) := by
    rw [spectrumAction_of_le X a b h]
    simp only [e, m, t, orderedAction, Category.assoc]
  have hPre : e ≫ (m ≫ t) ≍ m ≫ t := eqToHom_comp_heq _ _
  have hPost : m ≫ t ≍ m := comp_eqToHom_heq _ _
  exact (heq_of_eq hAction).trans (hPre.trans hPost)

/-- The complete Hom-object action respects actual source-first composition. -/
theorem spectrumAction_comp (X : SequentialSpectrum C K)
    (a b c : EnrichedIndex.Index K) :
    (X.level a.degree ◁ EnrichedIndex.indexComp K a b c) ≫ spectrumAction X a c =
      (α_ (X.level a.degree) (EnrichedIndex.indexHom K a b)
        (EnrichedIndex.indexHom K b c)).inv ≫
        (spectrumAction X a b ▷ EnrichedIndex.indexHom K b c) ≫
        spectrumAction X b c := by
  by_cases hab : a.degree ≤ b.degree
  · by_cases hbc : b.degree ≤ c.degree
    · let n := a.degree
      let p := b.degree - a.degree
      let q := c.degree - b.degree
      let A := X.level n
      let P := TensorPower.tensorPowObj K p
      let Q := TensorPower.tensorPowObj K q
      have hac := hab.trans hbc
      have hP : EnrichedIndex.indexHom K a b = P :=
        EnrichedIndex.indexHom_of_le K a b hab
      have hQ : EnrichedIndex.indexHom K b c = Q :=
        EnrichedIndex.indexHom_of_le K b c hbc
      have hN : b.degree = p + n := (Nat.sub_add_cancel hab).symm
      have hSum : c.degree - a.degree = p + q := by
        dsimp only [p, q]
        omega
      have hR : EnrichedIndex.indexHom K a c = TensorPower.tensorPowObj K (p + q) :=
        (EnrichedIndex.indexHom_of_le K a c hac).trans
          (congrArg (TensorPower.tensorPowObj K) hSum)
      have hLast : c.degree = q + (p + n) := by
        dsimp only [p, q, n]
        omega
      have hX : X.level b.degree = X.level (p + n) := congrArg X.level hN
      have hY : X.level c.degree = X.level (q + (p + n)) :=
        congrArg X.level hLast
      have hComp : EnrichedIndex.indexComp K a b c ≍
          EnrichedIndex.reversePair K p q := by
        simpa only [EnrichedIndex.indexComp, dite_eq_left hab, dite_eq_left hbc,
          Eq.mpr, Eq.mp, eqRec_heq_iff, heq_eqRec_iff, eqToHom_trans,
          eqToHom_comp_heq_iff, heq_eqToHom_comp_iff, comp_eqToHom_heq_iff,
          heq_comp_eqToHom_iff] using (HEq.refl (EnrichedIndex.reversePair K p q))
      have hAB : spectrumAction X a b ≍ orderedAction X p n :=
        spectrumAction_heq_orderedAction X a b hab
      have hBC : spectrumAction X b c ≍ orderedAction X q (p + n) :=
        (spectrumAction_heq_orderedAction X b c hbc).trans
          (orderedAction_congr X q b.degree q (p + n) rfl hN)
      have hAC : spectrumAction X a c ≍ orderedAction X (p + q) n ≫
          eqToHom (congrArg X.level
            (show (p + q) + n = q + (p + n) by omega)) :=
        (spectrumAction_heq_orderedAction X a c hac).trans
          ((orderedAction_congr X (c.degree - a.degree) n (p + q) n hSum rfl).trans
            (comp_eqToHom_heq (orderedAction X (p + q) n)
              (congrArg X.level (show (p + q) + n = q + (p + n) by omega))).symm)
      have hSource : X.level a.degree ⊗
          (EnrichedIndex.indexHom K a b ⊗ EnrichedIndex.indexHom K b c) =
          A ⊗ (P ⊗ Q) :=
        congrArg (fun V => A ⊗ V) (congrArg₂ (fun U V : C => U ⊗ V) hP hQ)
      have hAfter := congrArg (fun V => A ⊗ V) hR
      have hWhisker : (X.level a.degree ◁ EnrichedIndex.indexComp K a b c) ≍
          (A ◁ EnrichedIndex.reversePair K p q) :=
        heqWhiskerLeft _ _ (congrArg₂ (fun U V : C => U ⊗ V) hP hQ) hR
          hComp _ _ rfl
      have hL : (X.level a.degree ◁ EnrichedIndex.indexComp K a b c) ≫
          spectrumAction X a c ≍
          (A ◁ EnrichedIndex.reversePair K p q) ≫ orderedAction X (p + q) n ≫
            eqToHom (congrArg X.level
              (show (p + q) + n = q + (p + n) by omega)) :=
        heq_comp hSource hAfter hY hWhisker hAC
      have hMiddle := congrArg₂ (fun U V : C => U ⊗ V)
        (congrArg (fun V => A ⊗ V) hP) hQ
      have hAfterRight := congrArg₂ (fun U V : C => U ⊗ V) hX hQ
      have hWhiskerRight : (spectrumAction X a b ▷ EnrichedIndex.indexHom K b c) ≍
          (orderedAction X p n ▷ Q) :=
        heqWhiskerRight _ _ (congrArg (fun V => A ⊗ V) hP) hX hAB _ _ hQ
      have hTail : (spectrumAction X a b ▷ EnrichedIndex.indexHom K b c) ≫
          spectrumAction X b c ≍
          (orderedAction X p n ▷ Q) ≫ orderedAction X q (p + n) :=
        heq_comp hMiddle hAfterRight hY hWhiskerRight hBC
      have hRhs : (α_ (X.level a.degree) (EnrichedIndex.indexHom K a b)
            (EnrichedIndex.indexHom K b c)).inv ≫
          (spectrumAction X a b ▷ EnrichedIndex.indexHom K b c) ≫
          spectrumAction X b c ≍
          (α_ A P Q).inv ≫ (orderedAction X p n ▷ Q) ≫
            orderedAction X q (p + n) :=
        heq_comp hSource hMiddle hY (heqAssocInv _ _ _ _ _ _ rfl hP hQ) hTail
      have hCanonical := orderedAction_comp X p q n
      change (A ◁ EnrichedIndex.reversePair K p q) ≫ orderedAction X (p + q) n ≫
          eqToHom (congrArg X.level
            (show (p + q) + n = q + (p + n) by omega)) =
        (α_ A P Q).inv ≫ (orderedAction X p n ▷ Q) ≫
          orderedAction X q (p + n) at hCanonical
      exact eq_of_heq (hL.trans ((heq_of_eq hCanonical).trans hRhs.symm))
    · have hInner : IsInitial (EnrichedIndex.indexHom K a b ⊗
          EnrichedIndex.indexHom K b c) := by
        rw [EnrichedIndex.indexHom_of_gt K b c (Nat.lt_of_not_ge hbc)]
        exact MonoidalCategory.tensorInitialLeft _
      let _ : PreservesColimitsOfSize.{0, 0} (tensorLeft (X.level a.degree)) :=
        (ihom.adjunction (X.level a.degree)).leftAdjoint_preservesColimits
      have hDomain := IsInitial.isInitialObj (tensorLeft (X.level a.degree)) _ hInner
      exact hDomain.hom_ext _ _
  · have hInner : IsInitial (EnrichedIndex.indexHom K a b ⊗
        EnrichedIndex.indexHom K b c) := by
      rw [EnrichedIndex.indexHom_of_gt K a b (Nat.lt_of_not_ge hab)]
      exact MonoidalCategory.tensorInitialRight _
    let _ : PreservesColimitsOfSize.{0, 0} (tensorLeft (X.level a.degree)) :=
      (ihom.adjunction (X.level a.degree)).leftAdjoint_preservesColimits
    have hDomain := IsInitial.isInitialObj (tensorLeft (X.level a.degree)) _ hInner
    exact hDomain.hom_ext _ _

/-- The original zero iteration gives the actual right unit law for the action. -/
theorem spectrumAction_id (X : SequentialSpectrum C K) (a : EnrichedIndex.Index K) :
    (X.level a.degree ◁ EnrichedIndex.indexId K a) ≫ spectrumAction X a a =
      (ρ_ (X.level a.degree)).hom := by
  let A := X.level a.degree
  have hH := EnrichedIndex.indexHom_self K a
  have hWhisker : (A ◁ EnrichedIndex.indexId K a) ≍ 𝟙 (A ⊗ 𝟙_ C) := by
    unfold EnrichedIndex.indexId
    rw [whiskerLeft_eqToHom]
    exact eqToHom_heq_id_dom _ _ _
  have hAction : spectrumAction X a a ≍ (ρ_ A).hom := by
    have hZero : orderedAction X 0 a.degree ≍ (ρ_ A).hom := by
      let t := eqToHom (congrArg X.level (Nat.zero_add a.degree).symm)
      have hAction : orderedAction X 0 a.degree =
          ((β_ A (𝟙_ C)).hom ≫ (λ_ A).hom) ≫ t := by
        simp only [orderedAction, iteratedStructureMap_zero,
          TensorPower.tensorPowObj_zero, A, t, Category.assoc]
      have hPost : ((β_ A (𝟙_ C)).hom ≫ (λ_ A).hom) ≫ t ≍
          (β_ A (𝟙_ C)).hom ≫ (λ_ A).hom := comp_eqToHom_heq _ _
      exact (heq_of_eq hAction).trans
        (hPost.trans (heq_of_eq (braiding_leftUnitor A)))
    exact (spectrumAction_heq_orderedAction X a a (le_refl _)).trans
      ((orderedAction_congr X (a.degree - a.degree) a.degree 0 a.degree
        (Nat.sub_self _) rfl).trans hZero)
  have hAll : (A ◁ EnrichedIndex.indexId K a) ≫ spectrumAction X a a ≍
      𝟙 (A ⊗ 𝟙_ C) ≫ (ρ_ A).hom :=
    heq_comp rfl (congrArg (fun V => A ⊗ V) hH) rfl hWhisker hAction
  exact eq_of_heq (hAll.trans (heq_of_eq (Category.id_comp _)))

omit [BraidedCategory C] [MonoidalClosed C] [HasInitial C] in
private theorem iteration_one_recover (X : SequentialSpectrum C K) (n : ℕ) :
    ((λ_ K).inv ⊗ₘ 𝟙 (X.level n)) ≫ iteratedStructureMap X 1 n ≫
      eqToHom (congrArg X.level (Nat.one_add n)) = X.structureMap n := by
  rw [iteratedStructureMap_succ, iteratedStructureMap_zero]
  have hCore : ((λ_ K).inv ⊗ₘ 𝟙 (X.level n)) ≫
      (α_ (𝟙_ C) K (X.level n)).hom ≫
      (𝟙 (𝟙_ C) ⊗ₘ X.structureMap n) ≫
      (λ_ (X.level (n + 1))).hom = X.structureMap n := by
    simp only [tensorHom_id, id_tensorHom]
    rw [← leftUnitor_tensor_inv_assoc]
    exact (id_whiskerLeft_symm (X.structureMap n)).symm
  simp only [TensorPower.tensorPowObj_zero, Category.assoc]
  let tail : X.level (n + 1) ⟶ X.level (n + 1) :=
    eqToHom (congrArg X.level (Nat.zero_add (n + 1)).symm) ≫
      eqToHom (congrArg X.level
        ((Nat.add_succ 0 n).trans (Nat.succ_add 0 n).symm)) ≫
      eqToHom (congrArg X.level (Nat.one_add n))
  have hTailProof : (congrArg X.level (Nat.zero_add (n + 1)).symm).trans
      ((congrArg X.level
        ((Nat.add_succ 0 n).trans (Nat.succ_add 0 n).symm)).trans
        (congrArg X.level (Nat.one_add n))) = rfl := Subsingleton.elim _ _
  have hTail : tail = 𝟙 (X.level (n + 1)) := by
    unfold tail
    simp only [eqToHom_trans]
    rw [hTailProof, eqToHom_refl]
  have hCorePost := congrArg (fun z : K ⊗ X.level n ⟶ X.level (n + 1) => z ≫ tail) hCore
  calc
    _ = X.structureMap n ≫ tail := by
      rw [← hCorePost]
      unfold tail
      simp only [Category.assoc]
    _ = X.structureMap n := by rw [hTail, Category.comp_id]

/-- The successor action is the original structure map through the actual degree-one iso. -/
theorem spectrumAction_successor (X : SequentialSpectrum C K) (n : ℕ) :
    spectrumAction X (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1)) =
      (X.level n ◁ (EnrichedIndex.indexHomSuccessorIso K n).hom) ≫
        (β_ (X.level n) K).hom ≫ X.structureMap n := by
  let A := X.level n
  let H := EnrichedIndex.indexHom K (EnrichedIndex.degree K n)
    (EnrichedIndex.degree K (n + 1))
  let e := EnrichedIndex.indexHomSuccessorIso K n
  have hDiff : (n + 1) - n = 1 := by omega
  have hH : H = 𝟙_ C ⊗ K := by
    simpa only [H, EnrichedIndex.degree, hDiff, TensorPower.tensorPowObj_succ,
      TensorPower.tensorPowObj_zero] using
        EnrichedIndex.indexHom_of_le K (EnrichedIndex.degree K n)
          (EnrichedIndex.degree K (n + 1)) (Nat.le_succ n)
  have hUnit : e.hom ≍ (λ_ K).hom := by
    change (eqToHom hH ≫ (λ_ K).hom) ≍ (λ_ K).hom
    exact eqToHom_comp_heq _ _
  have hWhisker : (A ◁ e.hom) ≍ (A ◁ (λ_ K).hom) :=
    heqWhiskerLeft _ _ hH rfl hUnit A A rfl
  have hRhs : (A ◁ e.hom) ≫ (β_ A K).hom ≫ X.structureMap n ≍
      (A ◁ (λ_ K).hom) ≫ (β_ A K).hom ≫ X.structureMap n :=
    heq_comp (congrArg (fun V => A ⊗ V) hH) rfl rfl hWhisker (HEq.refl _)
  have hAction : spectrumAction X (EnrichedIndex.degree K n)
      (EnrichedIndex.degree K (n + 1)) ≍
      orderedAction X 1 n ≫ eqToHom (congrArg X.level (Nat.one_add n)) :=
    (spectrumAction_heq_orderedAction X _ _ (Nat.le_succ n)).trans
      ((orderedAction_congr X ((n + 1) - n) n 1 n hDiff rfl).trans
        (comp_eqToHom_heq (orderedAction X 1 n)
          (congrArg X.level (Nat.one_add n))).symm)
  have hIteration : iteratedStructureMap X 1 n ≫
      eqToHom (congrArg X.level (Nat.one_add n)) =
      ((λ_ K).hom ▷ A) ≫ X.structureMap n := by
    apply (cancel_epi ((λ_ K).inv ▷ A)).1
    calc
      _ = X.structureMap n := by
        have hRecover := iteration_one_recover X n
        convert hRecover using 1
        simp only [A, tensorHom_id, Nat.succ_eq_add_one]
        rfl
      _ = _ := by
        simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id,
          id_whiskerRight, Category.id_comp]
  have hBraid : (A ◁ (λ_ K).hom) ≫ (β_ A K).hom =
      (β_ A (𝟙_ C ⊗ K)).hom ≫ ((λ_ K).hom ▷ A) :=
    braiding_naturality_right A (λ_ K).hom
  have hCanonical : orderedAction X 1 n ≫
      eqToHom (congrArg X.level (Nat.one_add n)) =
      (A ◁ (λ_ K).hom) ≫ (β_ A K).hom ≫ X.structureMap n := by
    simp only [orderedAction, Category.assoc]
    change (β_ A (𝟙_ C ⊗ K)).hom ≫ iteratedStructureMap X 1 n ≫ _ = _
    have hFirst := congrArg
      (fun f : TensorPower.tensorPowObj K 1 ⊗ A ⟶ X.level (n + 1) =>
        (β_ A (TensorPower.tensorPowObj K 1)).hom ≫ f) hIteration
    have hLast := congrArg (fun f => f ≫ X.structureMap n) hBraid.symm
    exact hFirst.trans (by
      simpa only [TensorPower.tensorPowObj_succ, TensorPower.tensorPowObj_zero,
        Category.assoc] using hLast)
  exact eq_of_heq (hAction.trans ((heq_of_eq hCanonical).trans hRhs.symm))

/-- Send the original spectrum to its genuine full-Hom enriched functor. -/
def toEnrichedFunctor (K : C) (X : SequentialSpectrum C K) : Carrier K where
  toEnrichedFunctor :=
    { obj := fun a => X.level a.degree
      map := fun a b => MonoidalClosed.curry (spectrumAction X a b)
      map_id := fun a => by
        apply MonoidalClosed.uncurry_injective
        change MonoidalClosed.uncurry (EnrichedIndex.indexId K a ≫
          MonoidalClosed.curry (spectrumAction X a a)) =
          MonoidalClosed.uncurry (MonoidalClosed.id (X.level a.degree))
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
          MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry]
        exact spectrumAction_id X a
      map_comp := fun a b c => by
        apply MonoidalClosed.uncurry_injective
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
          MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_curry,
          MonoidalClosed.uncurry_curry]
        exact spectrumAction_comp X a b c }

/-- The forward carrier keeps every original level object. -/
theorem toEnrichedFunctor_obj (K : C) (X : SequentialSpectrum C K)
    (a : EnrichedIndex.Index K) :
    (toEnrichedFunctor K X).toEnrichedFunctor.obj a = X.level a.degree := rfl

/-- Its uncurried map is the complete original spectrum action. -/
theorem toEnrichedFunctor_uncurry_map (K : C) (X : SequentialSpectrum C K)
    (a b : EnrichedIndex.Index K) :
    MonoidalClosed.uncurry ((toEnrichedFunctor K X).toEnrichedFunctor.map a b) =
      spectrumAction X a b := MonoidalClosed.uncurry_curry _

/-- Original level components form a genuine unit-graded transformation. -/
def toEnrichedFunctorMap (K : C) {X Y : SequentialSpectrum C K} (f : X ⟶ Y) :
    toEnrichedFunctor K X ⟶ toEnrichedFunctor K Y :=
  GradedNatTrans.unitOfComponents (fun a => f.levelMap a.degree)
    (fun a b => by
      change MonoidalClosed.uncurry (MonoidalClosed.curry (spectrumAction X a b)) ≫
          f.levelMap b.degree =
        (f.levelMap a.degree ⊗ₘ 𝟙 (EnrichedIndex.indexHom K a b)) ≫
          MonoidalClosed.uncurry (MonoidalClosed.curry (spectrumAction Y a b))
      rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
      exact spectrumAction_naturality f a b)

/-- Forward morphisms keep the original level components. -/
theorem toEnrichedFunctorMap_component (K : C) {X Y : SequentialSpectrum C K}
    (f : X ⟶ Y) (a : EnrichedIndex.Index K) :
    EnrichedFunctorCat.component (toEnrichedFunctorMap K f) a = f.levelMap a.degree :=
  GradedNatTrans.unitOfComponents_component _ _ _

/-- The forward spectrum-to-functor presentation acts on genuine transformations. -/
def toEnrichedFunctors (K : C) : SequentialSpectrum C K ⥤ Carrier K where
  obj := toEnrichedFunctor K
  map := toEnrichedFunctorMap K
  map_id X := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [toEnrichedFunctorMap_component, EnrichedFunctorCat.component_id]
    rfl
  map_comp f g := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [toEnrichedFunctorMap_component, EnrichedFunctorCat.component_comp,
      toEnrichedFunctorMap_component, toEnrichedFunctorMap_component]
    rfl


/-- Recover the original K-left successor map using the inverse of the forward braid. -/
def fromEnrichedFunctor (K : C) (F : Carrier K) : SequentialSpectrum C K where
  level n := F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)
  structureMap n :=
    ((EnrichedIndex.indexHomSuccessorIso K n).inv ⊗ₘ
      𝟙 (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n))) ≫
      (β_ (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n))
        (EnrichedIndex.indexHom K (EnrichedIndex.degree K n)
          (EnrichedIndex.degree K (n + 1)))).inv ≫
      MonoidalClosed.uncurry
        (F.toEnrichedFunctor.map (EnrichedIndex.degree K n)
          (EnrichedIndex.degree K (n + 1)))

/-- Reconstruction keeps the original enriched object in each degree. -/
theorem fromEnrichedFunctor_level (K : C) (F : Carrier K) (n : ℕ) :
    (fromEnrichedFunctor K F).level n =
      F.toEnrichedFunctor.obj (EnrichedIndex.degree K n) := rfl

/-- Genuine Hom-object naturality gives the original successor compatibility. -/
def fromEnrichedFunctorMap (K : C) {F G : Carrier K} (a : F ⟶ G) :
    fromEnrichedFunctor K F ⟶ fromEnrichedFunctor K G where
  levelMap n := EnrichedFunctorCat.component a (EnrichedIndex.degree K n)
  naturality n := by
    let i := EnrichedIndex.degree K n
    let j := EnrichedIndex.degree K (n + 1)
    let H := EnrichedIndex.indexHom K i j
    let D : K ⟶ H := (EnrichedIndex.indexHomSuccessorIso K n).inv
    let X := F.toEnrichedFunctor.obj i
    let Y := G.toEnrichedFunctor.obj i
    let q : X ⟶ Y := EnrichedFunctorCat.component a i
    let q' := EnrichedFunctorCat.component a j
    let AF := MonoidalClosed.uncurry (F.toEnrichedFunctor.map i j)
    let AG := MonoidalClosed.uncurry (G.toEnrichedFunctor.map i j)
    have hNatural : AF ≫ q' = (q ⊗ₘ 𝟙 H) ≫ AG :=
      a.uncurriedNaturality i j
    have hTensor : (𝟙 K ⊗ₘ q) ≫ (D ⊗ₘ 𝟙 Y) =
        (D ⊗ₘ 𝟙 X) ≫ (𝟙 H ⊗ₘ q) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      simp only [Category.id_comp, Category.comp_id]
    have hBraid : (𝟙 H ⊗ₘ q) ≫ (β_ Y H).inv =
        (β_ X H).inv ≫ (q ⊗ₘ 𝟙 H) := by
      simpa only [id_tensorHom, tensorHom_id] using
        braiding_inv_naturality_right H q
    dsimp only [fromEnrichedFunctor]
    simp only [Category.assoc]
    change (K ◁ q) ≫ (D ⊗ₘ 𝟙 Y) ≫ (β_ Y H).inv ≫ AG =
      (D ⊗ₘ 𝟙 X) ≫ (β_ X H).inv ≫ AF ≫ q'
    calc
      _ = (𝟙 K ⊗ₘ q) ≫ (D ⊗ₘ 𝟙 Y) ≫ (β_ Y H).inv ≫ AG := by
        rw [id_tensorHom]
      _ = (D ⊗ₘ 𝟙 X) ≫ (𝟙 H ⊗ₘ q) ≫ (β_ Y H).inv ≫ AG := by
        simpa only [Category.assoc] using
          congrArg (fun m => m ≫ (β_ Y H).inv ≫ AG) hTensor
      _ = (D ⊗ₘ 𝟙 X) ≫ (β_ X H).inv ≫ (q ⊗ₘ 𝟙 H) ≫ AG := by
        simpa only [Category.assoc] using
          congrArg (fun m => (D ⊗ₘ 𝟙 X) ≫ m ≫ AG) hBraid
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun m => (D ⊗ₘ 𝟙 X) ≫ (β_ X H).inv ≫ m) hNatural.symm

/-- Reconstructed maps retain the actual ordinary components. -/
theorem fromEnrichedFunctorMap_levelMap (K : C) {F G : Carrier K}
    (a : F ⟶ G) (n : ℕ) :
    (fromEnrichedFunctorMap K a).levelMap n =
      EnrichedFunctorCat.component a (EnrichedIndex.degree K n) := rfl

/-- The reconstruction is a functor on genuine unit-graded transformations. -/
def fromEnrichedFunctors (K : C) : Carrier K ⥤ SequentialSpectrum C K where
  obj := fromEnrichedFunctor K
  map := fromEnrichedFunctorMap K
  map_id F := by
    apply SequentialSpectrum.hom_ext
    intro n
    exact EnrichedFunctorCat.component_id F (EnrichedIndex.degree K n)
  map_comp a b := by
    apply SequentialSpectrum.hom_ext
    intro n
    exact EnrichedFunctorCat.component_comp a b (EnrichedIndex.degree K n)

/-- The full enriched functor is determined by its objects and successor Hom maps.
The proof cancels actual forward composition isomorphisms on complete Hom objects. -/
theorem enrichedFunctor_eq_of_successor (K : C)
    (F G : EnrichedFunctor C (EnrichedIndex.Index K) C)
    (hObj : F.obj = G.obj)
    (hStep : ∀ n : ℕ,
      F.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1)) ≍
        G.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1))) : F = G := by
  rcases F with ⟨FObj, FMap, FId, FComp⟩
  rcases G with ⟨GObj, GMap, GId, GComp⟩
  change FObj = GObj at hObj
  subst GObj
  have hStep' (n : ℕ) :
      FMap (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1)) =
        GMap (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1)) :=
    eq_of_heq (hStep n)
  have hMap (a b : EnrichedIndex.Index K) : FMap a b = GMap a b := by
    rcases a with ⟨n⟩
    rcases b with ⟨m⟩
    by_cases hnm : n ≤ m
    · exact Nat.decreasingInduction (n := m)
        (motive := fun k _ =>
          FMap (EnrichedIndex.degree K k) (EnrichedIndex.degree K m) =
            GMap (EnrichedIndex.degree K k) (EnrichedIndex.degree K m))
        (fun k hk ih => by
          let _ : IsIso (EnrichedIndex.indexComp K
              (EnrichedIndex.degree K k) (EnrichedIndex.degree K (k + 1))
              (EnrichedIndex.degree K m)) :=
            indexComp_isIso_of_le K _ _ _ (Nat.le_succ k) hk
          apply (cancel_epi (EnrichedIndex.indexComp K
            (EnrichedIndex.degree K k) (EnrichedIndex.degree K (k + 1))
            (EnrichedIndex.degree K m))).1
          calc
            _ = (FMap (EnrichedIndex.degree K k) (EnrichedIndex.degree K (k + 1)) ⊗ₘ
                FMap (EnrichedIndex.degree K (k + 1)) (EnrichedIndex.degree K m)) ≫
                eComp C (FObj (EnrichedIndex.degree K k))
                  (FObj (EnrichedIndex.degree K (k + 1)))
                  (FObj (EnrichedIndex.degree K m)) :=
              FComp (EnrichedIndex.degree K k) (EnrichedIndex.degree K (k + 1))
                (EnrichedIndex.degree K m)
            _ = (GMap (EnrichedIndex.degree K k) (EnrichedIndex.degree K (k + 1)) ⊗ₘ
                GMap (EnrichedIndex.degree K (k + 1)) (EnrichedIndex.degree K m)) ≫
                eComp C (FObj (EnrichedIndex.degree K k))
                  (FObj (EnrichedIndex.degree K (k + 1)))
                  (FObj (EnrichedIndex.degree K m)) :=
              congrArg (fun q => q ≫ eComp C (FObj (EnrichedIndex.degree K k))
                (FObj (EnrichedIndex.degree K (k + 1)))
                (FObj (EnrichedIndex.degree K m)))
                  (congrArg₂ (fun p q => p ⊗ₘ q) (hStep' k) ih)
            _ = _ :=
              (GComp (EnrichedIndex.degree K k) (EnrichedIndex.degree K (k + 1))
                (EnrichedIndex.degree K m)).symm)
        (by
          let _ : IsIso (EnrichedIndex.indexId K (EnrichedIndex.degree K m)) := by
            unfold EnrichedIndex.indexId
            infer_instance
          apply (cancel_epi (EnrichedIndex.indexId K (EnrichedIndex.degree K m))).1
          exact (FId (EnrichedIndex.degree K m)).trans
            (GId (EnrichedIndex.degree K m)).symm)
        hnm
    · have hInitial : IsInitial (EnrichedIndex.indexHom K
          (EnrichedIndex.degree K n) (EnrichedIndex.degree K m)) := by
        rw [EnrichedIndex.indexHom_of_gt K (EnrichedIndex.degree K n)
          (EnrichedIndex.degree K m) (Nat.lt_of_not_ge hnm)]
        exact initialIsInitial
      exact hInitial.hom_ext _ _
  have hMaps : FMap = GMap := funext fun a => funext fun b => hMap a b
  cases hMaps
  rfl

/-- Forward then backward keeps the original successor structure map. -/
theorem from_to_structureMap (K : C) (X : SequentialSpectrum C K) (n : ℕ) :
    (fromEnrichedFunctor K (toEnrichedFunctor K X)).structureMap n =
      X.structureMap n := by
  let A := X.level n
  let H := EnrichedIndex.indexHom K (EnrichedIndex.degree K n)
    (EnrichedIndex.degree K (n + 1))
  let e : H ≅ K := EnrichedIndex.indexHomSuccessorIso K n
  have hUncurry : MonoidalClosed.uncurry
      ((toEnrichedFunctor K X).toEnrichedFunctor.map
        (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1))) =
      spectrumAction X (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1)) :=
    toEnrichedFunctor_uncurry_map K X _ _
  have hForward := spectrumAction_successor X n
  have hFirst : (fromEnrichedFunctor K (toEnrichedFunctor K X)).structureMap n =
      (e.inv ▷ A) ≫ (β_ A H).inv ≫ (A ◁ e.hom) ≫ (β_ A K).hom ≫ X.structureMap n := by
    have h := congrArg (fun f : A ⊗ H ⟶ X.level (n + 1) =>
      (e.inv ▷ A) ≫ (β_ A H).inv ≫ f) (hUncurry.trans hForward)
    convert h using 1
    simp only [fromEnrichedFunctor, toEnrichedFunctor, EnrichedIndex.degree,
      A, H, e, tensorHom_id]
    rfl
  have hBraid := braiding_naturality_right A e.hom
  have hMiddle : (e.inv ▷ A) ≫ (β_ A H).inv ≫ (A ◁ e.hom) ≫
      (β_ A K).hom ≫ X.structureMap n =
      (e.inv ▷ A) ≫ (β_ A H).inv ≫ (β_ A H).hom ≫
        (e.hom ▷ A) ≫ X.structureMap n := by
    simpa only [Category.assoc] using
      congrArg (fun q : A ⊗ H ⟶ K ⊗ A =>
        (e.inv ▷ A) ≫ (β_ A H).inv ≫ q ≫ X.structureMap n) hBraid
  have hLast : (e.inv ▷ A) ≫ (β_ A H).inv ≫ (β_ A H).hom ≫
      (e.hom ▷ A) ≫ X.structureMap n = X.structureMap n := by
    rw [Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp]
  exact hFirst.trans (hMiddle.trans hLast)

/-- Both level objects and successor maps reconstruct the original spectrum. -/
theorem from_to (K : C) (X : SequentialSpectrum C K) :
    fromEnrichedFunctor K (toEnrichedFunctor K X) = X := by
  rcases X with ⟨levels, sigma⟩
  change SequentialSpectrum.mk levels _ = SequentialSpectrum.mk levels sigma
  congr 1
  funext n
  exact from_to_structureMap K ⟨levels, sigma⟩ n

/-- Backward then forward recovers the complete successor Hom map. -/
theorem to_from_successor_map (K : C) (F : Carrier K) (n : ℕ) :
    (toEnrichedFunctor K (fromEnrichedFunctor K F)).toEnrichedFunctor.map
        (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1)) =
      F.toEnrichedFunctor.map (EnrichedIndex.degree K n)
        (EnrichedIndex.degree K (n + 1)) := by
  let A := F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)
  let H := EnrichedIndex.indexHom K (EnrichedIndex.degree K n)
    (EnrichedIndex.degree K (n + 1))
  let e := EnrichedIndex.indexHomSuccessorIso K n
  let act := MonoidalClosed.uncurry (F.toEnrichedFunctor.map
    (EnrichedIndex.degree K n) (EnrichedIndex.degree K (n + 1)))
  apply MonoidalClosed.uncurry_injective
  rw [toEnrichedFunctor_uncurry_map, spectrumAction_successor]
  change (A ◁ e.hom) ≫ (β_ A K).hom ≫ (e.inv ⊗ₘ 𝟙 A) ≫
      (β_ A H).inv ≫ act = act
  have hBraid := braiding_naturality_right A e.hom
  calc
    _ = (β_ A H).hom ≫ (e.hom ▷ A) ≫ (e.inv ▷ A) ≫
        (β_ A H).inv ≫ act := by
      simpa only [tensorHom_id, Category.assoc] using
        congrArg (fun q : A ⊗ H ⟶ K ⊗ A =>
          q ≫ (e.inv ▷ A) ≫ (β_ A H).inv ≫ act) hBraid
    _ = act := by
      rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight,
        Category.id_comp, Iso.hom_inv_id_assoc]

/-- The reconstructed functor agrees on every Hom object, by successor determination. -/
theorem to_from_enrichedFunctor (K : C) (F : Carrier K) :
    (toEnrichedFunctor K (fromEnrichedFunctor K F)).toEnrichedFunctor =
      F.toEnrichedFunctor := by
  apply enrichedFunctor_eq_of_successor K
  · funext a
    cases a
    rfl
  · intro n
    exact heq_of_eq (to_from_successor_map K F n)

/-- Both reconstructions hold on the genuine enriched-functor objects. -/
theorem to_from (K : C) (F : Carrier K) :
    toEnrichedFunctor K (fromEnrichedFunctor K F) = F :=
  congrArg (fun f : EnrichedFunctor C (EnrichedIndex.Index K) C =>
    (⟨f⟩ : Carrier K)) (to_from_enrichedFunctor K F)

private theorem enrichedUncurry_heq_of_eq
    (F G : EnrichedFunctor C (EnrichedIndex.Index K) C) (h : F = G)
    (a b : EnrichedIndex.Index K) :
    MonoidalClosed.uncurry (F.map a b) ≍ MonoidalClosed.uncurry (G.map a b) := by
  cases h
  rfl

/-- Every higher enriched action is the original iteration of the recovered successor map. -/
theorem higher_action_recovery (K : C) (F : Carrier K)
    (a b : EnrichedIndex.Index K) :
    spectrumAction (fromEnrichedFunctor K F) a b ≍
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) :=
  (heq_of_eq (toEnrichedFunctor_uncurry_map K (fromEnrichedFunctor K F) a b)).symm.trans
    (enrichedUncurry_heq_of_eq _ _ (to_from_enrichedFunctor K F) a b)

/-- The spectrum-side reconstruction iso uses literal identity level maps. -/
def spectrumUnitIsoApp (K : C) (X : SequentialSpectrum C K) :
    X ≅ (toEnrichedFunctors K ⋙ fromEnrichedFunctors K).obj X where
  hom :=
    { levelMap := fun n => 𝟙 (X.level n)
      naturality := fun n => by
        change (K ◁ 𝟙 (X.level n)) ≫
            (fromEnrichedFunctor K (toEnrichedFunctor K X)).structureMap n =
          X.structureMap n ≫ 𝟙 (X.level (n + 1))
        rw [from_to_structureMap, whiskerLeft_id]
        dsimp only [fromEnrichedFunctor, toEnrichedFunctor, EnrichedIndex.degree]
        exact (Category.id_comp (X.structureMap n)).trans
          (Category.comp_id (X.structureMap n)).symm }
  inv :=
    { levelMap := fun n => 𝟙 (X.level n)
      naturality := fun n => by
        change (K ◁ 𝟙 (X.level n)) ≫ X.structureMap n =
          (fromEnrichedFunctor K (toEnrichedFunctor K X)).structureMap n ≫
            𝟙 (X.level (n + 1))
        rw [from_to_structureMap, whiskerLeft_id]
        dsimp only [fromEnrichedFunctor, toEnrichedFunctor, EnrichedIndex.degree]
        exact (Category.id_comp (X.structureMap n)).trans
          (Category.comp_id (X.structureMap n)).symm }
  hom_inv_id := by
    apply SequentialSpectrum.hom_ext
    intro n
    exact Category.id_comp _
  inv_hom_id := by
    apply SequentialSpectrum.hom_ext
    intro n
    exact Category.id_comp _

/-- The unit's forward component is the original identity level map. -/
@[simp]
theorem spectrumUnitIsoApp_hom_levelMap (K : C) (X : SequentialSpectrum C K) (n : ℕ) :
    (spectrumUnitIsoApp K X).hom.levelMap n = 𝟙 (X.level n) := rfl

/-- The unit's inverse component is the original identity level map. -/
@[simp]
theorem spectrumUnitIsoApp_inv_levelMap (K : C) (X : SequentialSpectrum C K) (n : ℕ) :
    (spectrumUnitIsoApp K X).inv.levelMap n = 𝟙 (X.level n) := rfl

/-- The enriched reconstruction iso keeps literal identity components and full naturality. -/
def enrichedCounitIsoApp (K : C) (F : Carrier K) :
    (fromEnrichedFunctors K ⋙ toEnrichedFunctors K).obj F ≅ F := by
  let F0 := F.toEnrichedFunctor
  let G0 := (toEnrichedFunctor K (fromEnrichedFunctor K F)).toEnrichedFunctor
  have hFG : G0 = F0 := to_from_enrichedFunctor K F
  let qHom : ∀ a, G0.obj a ⟶ F0.obj a :=
    fun ⟨n⟩ => 𝟙 (F0.obj (EnrichedIndex.degree K n))
  let qInv : ∀ a, F0.obj a ⟶ G0.obj a :=
    fun ⟨n⟩ => 𝟙 (F0.obj (EnrichedIndex.degree K n))
  have hHomNatural : ∀ a b,
      MonoidalClosed.uncurry (G0.map a b) ≫ qHom b =
        (qHom a ⊗ₘ 𝟙 (a ⟶[C] b)) ≫ MonoidalClosed.uncurry (F0.map a b) := by
    rintro ⟨n⟩ ⟨m⟩
    let A := F0.obj (EnrichedIndex.degree K n)
    let B := F0.obj (EnrichedIndex.degree K m)
    let H := EnrichedIndex.indexHom K (EnrichedIndex.degree K n) (EnrichedIndex.degree K m)
    let a : A ⊗ H ⟶ B :=
      MonoidalClosed.uncurry (G0.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K m))
    let b : A ⊗ H ⟶ B :=
      MonoidalClosed.uncurry (F0.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K m))
    have hMap : G0.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K m) =
        F0.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K m) :=
      eq_of_heq (EnrichedFunctor.map_heq_of_eq G0 F0 hFG _ _)
    have hAction : a = b := congrArg MonoidalClosed.uncurry hMap
    have hTensor : (𝟙 A ⊗ₘ 𝟙 H) = 𝟙 (A ⊗ H) := by
      rw [tensorHom_id, id_whiskerRight]
    have hPre : (𝟙 A ⊗ₘ 𝟙 H) ≫ b = b :=
      (congrArg (fun f : A ⊗ H ⟶ A ⊗ H => f ≫ b) hTensor).trans (Category.id_comp b)
    change a ≫ 𝟙 B = (𝟙 A ⊗ₘ 𝟙 H) ≫ b
    exact (Category.comp_id a).trans (hAction.trans hPre.symm)
  have hInvNatural : ∀ a b,
      MonoidalClosed.uncurry (F0.map a b) ≫ qInv b =
        (qInv a ⊗ₘ 𝟙 (a ⟶[C] b)) ≫ MonoidalClosed.uncurry (G0.map a b) := by
    rintro ⟨n⟩ ⟨m⟩
    let A := F0.obj (EnrichedIndex.degree K n)
    let B := F0.obj (EnrichedIndex.degree K m)
    let H := EnrichedIndex.indexHom K (EnrichedIndex.degree K n) (EnrichedIndex.degree K m)
    let a : A ⊗ H ⟶ B :=
      MonoidalClosed.uncurry (F0.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K m))
    let b : A ⊗ H ⟶ B :=
      MonoidalClosed.uncurry (G0.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K m))
    have hMap : G0.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K m) =
        F0.map (EnrichedIndex.degree K n) (EnrichedIndex.degree K m) :=
      eq_of_heq (EnrichedFunctor.map_heq_of_eq G0 F0 hFG _ _)
    have hAction : a = b := (congrArg MonoidalClosed.uncurry hMap).symm
    have hTensor : (𝟙 A ⊗ₘ 𝟙 H) = 𝟙 (A ⊗ H) := by
      rw [tensorHom_id, id_whiskerRight]
    have hPre : (𝟙 A ⊗ₘ 𝟙 H) ≫ b = b :=
      (congrArg (fun f : A ⊗ H ⟶ A ⊗ H => f ≫ b) hTensor).trans (Category.id_comp b)
    change a ≫ 𝟙 B = (𝟙 A ⊗ₘ 𝟙 H) ≫ b
    exact (Category.comp_id a).trans (hAction.trans hPre.symm)
  let hom : (fromEnrichedFunctors K ⋙ toEnrichedFunctors K).obj F ⟶ F :=
    GradedNatTrans.unitOfComponents (F' := G0) (G' := F0) qHom hHomNatural
  let inv : F ⟶ (fromEnrichedFunctors K ⋙ toEnrichedFunctors K).obj F :=
    GradedNatTrans.unitOfComponents (F' := F0) (G' := G0) qInv hInvNatural
  have hHom (n : ℕ) : EnrichedFunctorCat.component hom (EnrichedIndex.degree K n) =
      𝟙 (F0.obj (EnrichedIndex.degree K n)) :=
    GradedNatTrans.unitOfComponents_component qHom hHomNatural _
  have hInv (n : ℕ) : EnrichedFunctorCat.component inv (EnrichedIndex.degree K n) =
      𝟙 (F0.obj (EnrichedIndex.degree K n)) :=
    GradedNatTrans.unitOfComponents_component qInv hInvNatural _
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply EnrichedFunctorCat.hom_ext
        rintro ⟨n⟩
        change EnrichedFunctorCat.component (hom ≫ inv) (EnrichedIndex.degree K n) = _
        rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id, hHom, hInv]
        exact Category.id_comp _
      inv_hom_id := by
        apply EnrichedFunctorCat.hom_ext
        rintro ⟨n⟩
        change EnrichedFunctorCat.component (inv ≫ hom) (EnrichedIndex.degree K n) = _
        rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id, hInv, hHom]
        exact Category.id_comp _ }

/-- The enriched counit's forward degree component is the original identity. -/
@[simp]
theorem enrichedCounitIsoApp_hom_component (K : C) (F : Carrier K) (n : ℕ) :
    EnrichedFunctorCat.component
        (F := (toEnrichedFunctors K).obj ((fromEnrichedFunctors K).obj F))
        (G := F) (enrichedCounitIsoApp K F).hom
        (EnrichedIndex.degree K n) =
      𝟙 (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)) := by
  exact GradedNatTrans.unitOfComponents_component
    (V := C)
    (F' := (toEnrichedFunctor K (fromEnrichedFunctor K F)).toEnrichedFunctor)
    (G' := F.toEnrichedFunctor)
    _ _ (EnrichedIndex.degree K n)

/-- The enriched counit's inverse degree component is the original identity. -/
@[simp]
theorem enrichedCounitIsoApp_inv_component (K : C) (F : Carrier K) (n : ℕ) :
    EnrichedFunctorCat.component (F := F)
        (G := (toEnrichedFunctors K).obj ((fromEnrichedFunctors K).obj F))
        (enrichedCounitIsoApp K F).inv
        (EnrichedIndex.degree K n) =
      𝟙 (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)) := by
  exact GradedNatTrans.unitOfComponents_component
    (V := C)
    (F' := F.toEnrichedFunctor)
    (G' := (toEnrichedFunctor K (fromEnrichedFunctor K F)).toEnrichedFunctor)
    _ _ (EnrichedIndex.degree K n)

/-- The spectrum reconstruction is natural on the original morphisms. -/
def spectrumUnitIso (K : C) :
    𝟭 (SequentialSpectrum C K) ≅ toEnrichedFunctors K ⋙ fromEnrichedFunctors K :=
  NatIso.ofComponents (spectrumUnitIsoApp K) (fun {X Y} f => by
    apply SequentialSpectrum.hom_ext
    intro n
    change f.levelMap n ≫ (spectrumUnitIsoApp K Y).hom.levelMap n =
      (spectrumUnitIsoApp K X).hom.levelMap n ≫
        (fromEnrichedFunctorMap K (toEnrichedFunctorMap K f)).levelMap n
    rw [spectrumUnitIsoApp_hom_levelMap, spectrumUnitIsoApp_hom_levelMap,
      fromEnrichedFunctorMap_levelMap, toEnrichedFunctorMap_component]
    dsimp only [EnrichedIndex.degree]
    exact (Category.comp_id (f.levelMap n)).trans (Category.id_comp (f.levelMap n)).symm)

/-- The enriched reconstruction is natural on genuine unit-graded transformations. -/
def enrichedCounitIso (K : C) :
    fromEnrichedFunctors K ⋙ toEnrichedFunctors K ≅ 𝟭 (Carrier K) :=
  NatIso.ofComponents (enrichedCounitIsoApp K) (fun {F G} a => by
    apply EnrichedFunctorCat.hom_ext
    rintro ⟨n⟩
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp]
    change EnrichedFunctorCat.component
        (toEnrichedFunctorMap K (fromEnrichedFunctorMap K a)) (EnrichedIndex.degree K n) ≫
        EnrichedFunctorCat.component (enrichedCounitIsoApp K G).hom (EnrichedIndex.degree K n) =
      EnrichedFunctorCat.component (enrichedCounitIsoApp K F).hom (EnrichedIndex.degree K n) ≫
        EnrichedFunctorCat.component a (EnrichedIndex.degree K n)
    rw [toEnrichedFunctorMap_component, fromEnrichedFunctorMap_levelMap,
      enrichedCounitIsoApp_hom_component, enrichedCounitIsoApp_hom_component]
    dsimp only [EnrichedIndex.degree]
    exact (Category.comp_id (EnrichedFunctorCat.component a (EnrichedIndex.degree K n))).trans
      (Category.id_comp (EnrichedFunctorCat.component a (EnrichedIndex.degree K n))).symm)

/-- The original sequential spectrum carrier is equivalent to genuine enriched functors. -/
def enrichedEquivalence (K : C) : SequentialSpectrum C K ≌ Carrier K where
  functor := toEnrichedFunctors K
  inverse := fromEnrichedFunctors K
  unitIso := spectrumUnitIso K
  counitIso := enrichedCounitIso K
  functor_unitIso_comp X := by
    apply EnrichedFunctorCat.hom_ext
    rintro ⟨n⟩
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id]
    change EnrichedFunctorCat.component
        (toEnrichedFunctorMap K (spectrumUnitIsoApp K X).hom) (EnrichedIndex.degree K n) ≫
        EnrichedFunctorCat.component (enrichedCounitIsoApp K (toEnrichedFunctor K X)).hom
          (EnrichedIndex.degree K n) = 𝟙 (X.level n)
    rw [toEnrichedFunctorMap_component, spectrumUnitIsoApp_hom_levelMap,
      enrichedCounitIsoApp_hom_component]
    dsimp only [toEnrichedFunctor, EnrichedIndex.degree]
    exact Category.id_comp (𝟙 (X.level n))

/-- Evaluation of genuine enriched functors is the actual object and component projection. -/
abbrev functorEvaluation (K : C) (n : ℕ) : Carrier K ⥤ C :=
  EnrichedFunctorCat.evaluation (V := C) (EnrichedIndex.degree K n)

/-- Forward presentation commutes with the original evaluation, on objects and maps. -/
def toEvaluationIso (K : C) (n : ℕ) :
    toEnrichedFunctors K ⋙ (EnrichedFunctorCat.evaluation (V := C)
        (EnrichedIndex.degree K n)) ≅ evaluation K n :=
  NatIso.ofComponents (fun X => Iso.refl (X.level n)) (fun {X Y} f => by
    change EnrichedFunctorCat.component (toEnrichedFunctorMap K f)
        (EnrichedIndex.degree K n) ≫ 𝟙 (Y.level n) =
      𝟙 (X.level n) ≫ f.levelMap n
    rw [toEnrichedFunctorMap_component]
    dsimp only [toEnrichedFunctor, EnrichedIndex.degree]
    exact (Category.comp_id (f.levelMap n)).trans (Category.id_comp (f.levelMap n)).symm)

/-- Backward presentation commutes with the same actual evaluation projections. -/
def fromEvaluationIso (K : C) (n : ℕ) :
    fromEnrichedFunctors K ⋙ evaluation K n ≅ (EnrichedFunctorCat.evaluation (V := C)
        (EnrichedIndex.degree K n)) :=
  NatIso.ofComponents
    (fun F => Iso.refl (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)))
    (fun {F G} a => by
      change (fromEnrichedFunctorMap K a).levelMap n ≫ 𝟙 _ =
        𝟙 _ ≫ EnrichedFunctorCat.component a (EnrichedIndex.degree K n)
      rw [fromEnrichedFunctorMap_levelMap]
      dsimp only [fromEnrichedFunctor]
      exact (Category.comp_id (EnrichedFunctorCat.component a (EnrichedIndex.degree K n))).trans
        (Category.id_comp (EnrichedFunctorCat.component a (EnrichedIndex.degree K n))).symm)

/-- The backward evaluation comparison is the literal identity on the selected degree object. -/
@[simp]
theorem fromEvaluationIso_hom_app (K : C) (n : ℕ) (F : Carrier K) :
    (fromEvaluationIso K n).hom.app F =
      𝟙 (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)) := rfl

/-- Its inverse also retains that same identity projection. -/
@[simp]
theorem fromEvaluationIso_inv_app (K : C) (n : ℕ) (F : Carrier K) :
    (fromEvaluationIso K n).inv.app F =
      𝟙 (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)) := rfl

/-- The equivalence Hom map uses the actual unit and original component reconstruction. -/
theorem enrichedEquivalence_homEquiv (K : C) {X : SequentialSpectrum C K}
    {F : Carrier K} (f : (toEnrichedFunctors K).obj X ⟶ F) :
    ((enrichedEquivalence K).toAdjunction.homEquiv X F) f =
      (spectrumUnitIsoApp K X).hom ≫ (fromEnrichedFunctors K).map f :=
  (enrichedEquivalence K).toAdjunction.homEquiv_apply X F f

/-- The inverse Hom map uses the actual counit and original forward component map. -/
theorem enrichedEquivalence_homEquiv_symm (K : C) {X : SequentialSpectrum C K}
    {F : Carrier K} (g : X ⟶ (fromEnrichedFunctors K).obj F) :
    ((enrichedEquivalence K).toAdjunction.homEquiv X F).symm g =
      (toEnrichedFunctors K).map g ≫ (enrichedCounitIsoApp K F).hom :=
  (enrichedEquivalence K).toAdjunction.homEquiv_symm_apply X F g

section OriginalFreeComparison

/- These are the original particular Day-extension and preservation dictionaries.
They belong only to the original free/evaluation comparison, not to the carrier equivalence. -/
variable
  [∀ (F G : Sequence.Index ⥤ C),
    (tensor Sequence.Index).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ Sequence.Index)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ C))]
  [∀ (W : C) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Sequence.Index) d) (tensorLeft W)]
  [∀ (W : C) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Sequence.Index) d) (tensorRight W)]
  [∀ (W : C) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorLeft W)]
  [∀ (W : C) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorRight W)]
  [∀ (W : C) (d : Sequence.Index × Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((𝟭 Sequence.Index).prod (Functor.fromPUnit.{0} (𝟙_ Sequence.Index))) d)
      (tensorRight W)]
  [∀ (W : C) (d : Sequence.Index × Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow ((tensor Sequence.Index).prod (𝟭 Sequence.Index)) d)
      (tensorRight W)]
  [∀ i j : Sequence.Index, HasCoproductsOfShape (i ⟶ j) C]

/-- The actual original free spectrum, presented as a genuine enriched functor. -/
def enrichedFreeAt (K : C) (n : ℕ) : C ⥤ Carrier K :=
  freeAt K n ⋙ toEnrichedFunctors K

/-- Its original generator morphism retains every level component. -/
theorem enrichedFreeAt_map_component (K : C) (n : ℕ) {A B : C} (f : A ⟶ B) (m : ℕ) :
    EnrichedFunctorCat.component ((enrichedFreeAt K n).map f) (EnrichedIndex.degree K m) =
      ((freeAt K n).map f).levelMap m :=
  toEnrichedFunctorMap_component K ((freeAt K n).map f) (EnrichedIndex.degree K m)

/-- This is the original free/evaluation adjunction composed with the actual carrier equivalence. -/
def enrichedFreeAtEvaluationAdjunction (K : C) (n : ℕ) :
    enrichedFreeAt K n ⊣ (EnrichedFunctorCat.evaluation (V := C) (EnrichedIndex.degree K n)) :=
  ((freeAtEvaluationAdjunction K n).comp (enrichedEquivalence K).toAdjunction).ofNatIsoRight
    (fromEvaluationIso K n)

/-- The adjunct is computed by the original Hom equivalence on the reconstructed actual morphism. -/
theorem originalAdjunction_homEquiv (K : C) (n : ℕ) {A : C} {F : Carrier K}
    (f : (enrichedFreeAt K n).obj A ⟶ F) :
    ((enrichedFreeAtEvaluationAdjunction K n).homEquiv A F) f =
      ((freeAtEvaluationAdjunction K n).homEquiv A ((fromEnrichedFunctors K).obj F))
        ((spectrumUnitIsoApp K ((freeAt K n).obj A)).hom ≫
          (fromEnrichedFunctors K).map f) := by
  let original : freeAt K n ⊣ evaluation K n := freeAtEvaluationAdjunction K n
  let equiv : toEnrichedFunctors K ⊣ fromEnrichedFunctors K :=
    (enrichedEquivalence K).toAdjunction
  let base : freeAt K n ⋙ toEnrichedFunctors K ⊣
      fromEnrichedFunctors K ⋙ evaluation K n := original.comp equiv
  let e : fromEnrichedFunctors K ⋙ evaluation K n ≅ (EnrichedFunctorCat.evaluation (V := C)
      (EnrichedIndex.degree K n)) :=
    fromEvaluationIso K n
  have hApply : ((base.ofNatIsoRight e).homEquiv A F) f =
      (base.homEquiv A F) f ≫ e.hom.app F :=
    Adjunction.homEquiv_ofNatIsoRight_apply base e f
  have hComp : (base.homEquiv A F) f =
      (original.homEquiv A ((fromEnrichedFunctors K).obj F))
        ((equiv.homEquiv ((freeAt K n).obj A) F) f) :=
    congrArg (fun H => (H A F) f) (Adjunction.comp_homEquiv original equiv)
  have hIso : e.hom.app F = 𝟙 (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)) :=
    fromEvaluationIso_hom_app K n F
  have hEquiv : (equiv.homEquiv ((freeAt K n).obj A) F) f =
      (spectrumUnitIsoApp K ((freeAt K n).obj A)).hom ≫
        (fromEnrichedFunctors K).map f := enrichedEquivalence_homEquiv K f
  have hPost : (base.homEquiv A F) f ≫ e.hom.app F =
      (original.homEquiv A ((fromEnrichedFunctors K).obj F))
        ((equiv.homEquiv ((freeAt K n).obj A) F) f) ≫ 𝟙 _ :=
    congrArg₂ (fun a b => a ≫ b) hComp hIso
  have hLast : (original.homEquiv A ((fromEnrichedFunctors K).obj F))
        ((equiv.homEquiv ((freeAt K n).obj A) F) f) ≫ 𝟙 _ =
      (original.homEquiv A ((fromEnrichedFunctors K).obj F))
        ((spectrumUnitIsoApp K ((freeAt K n).obj A)).hom ≫
          (fromEnrichedFunctors K).map f) :=
    (Category.comp_id _).trans
      (congrArg (original.homEquiv A ((fromEnrichedFunctors K).obj F)) hEquiv)
  exact hApply.trans (hPost.trans hLast)

/-- The inverse adjunct is the original inverse adjunct followed by the full enriched counit. -/
theorem originalAdjunction_homEquiv_symm (K : C) (n : ℕ) {A : C} {F : Carrier K}
    (f : A ⟶ F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)) :
    ((enrichedFreeAtEvaluationAdjunction K n).homEquiv A F).symm f =
      (toEnrichedFunctors K).map
          (((freeAtEvaluationAdjunction K n).homEquiv A ((fromEnrichedFunctors K).obj F)).symm f) ≫
        (enrichedCounitIsoApp K F).hom := by
  let original : freeAt K n ⊣ evaluation K n := freeAtEvaluationAdjunction K n
  let equiv : toEnrichedFunctors K ⊣ fromEnrichedFunctors K :=
    (enrichedEquivalence K).toAdjunction
  let base : freeAt K n ⋙ toEnrichedFunctors K ⊣
      fromEnrichedFunctors K ⋙ evaluation K n := original.comp equiv
  let e : fromEnrichedFunctors K ⋙ evaluation K n ≅ (EnrichedFunctorCat.evaluation (V := C)
      (EnrichedIndex.degree K n)) :=
    fromEvaluationIso K n
  have hApply : ((base.ofNatIsoRight e).homEquiv A F).symm f =
      (base.homEquiv A F).symm (f ≫ e.inv.app F) :=
    Adjunction.homEquiv_ofNatIsoRight_symm_apply base e f
  have hIso : e.inv.app F = 𝟙 (F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)) :=
    fromEvaluationIso_inv_app K n F
  have hInput : f ≫ e.inv.app F = f :=
    (congrArg (fun g => f ≫ g) hIso).trans (Category.comp_id f)
  have hComp : (base.homEquiv A F).symm f =
      (equiv.homEquiv ((freeAt K n).obj A) F).symm
        ((original.homEquiv A ((fromEnrichedFunctors K).obj F)).symm f) :=
    congrArg (fun H => (H A F).symm f) (Adjunction.comp_homEquiv original equiv)
  have hLast : (equiv.homEquiv ((freeAt K n).obj A) F).symm
        ((original.homEquiv A ((fromEnrichedFunctors K).obj F)).symm f) =
      (toEnrichedFunctors K).map
        ((original.homEquiv A ((fromEnrichedFunctors K).obj F)).symm f) ≫
          (enrichedCounitIsoApp K F).hom :=
    enrichedEquivalence_homEquiv_symm K _
  exact hApply.trans ((congrArg (base.homEquiv A F).symm hInput).trans
    (hComp.trans hLast))

/-- The chosen free generator unit is exactly the original unit, not a new coefficient map. -/
theorem originalAdjunction_unit_app (K : C) (n : ℕ) (A : C) :
    (enrichedFreeAtEvaluationAdjunction K n).unit.app A =
      (freeAtEvaluationAdjunction K n).unit.app A := by
  let X : SequentialSpectrum C K := (freeAt K n).obj A
  let B : C := X.level n
  let original : freeAt K n ⊣ evaluation K n := freeAtEvaluationAdjunction K n
  let adj : enrichedFreeAt K n ⊣ (EnrichedFunctorCat.evaluation (V := C)
      (EnrichedIndex.degree K n)) :=
    enrichedFreeAtEvaluationAdjunction K n
  let R : Carrier K ⥤ SequentialSpectrum C K := fromEnrichedFunctors K
  let F : Carrier K := (enrichedFreeAt K n).obj A
  let e : X ≅ R.obj F := spectrumUnitIsoApp K X
  have hId : R.map (𝟙 F) = 𝟙 (R.obj F) := R.map_id F
  have hMap : e.hom ≫ R.map (𝟙 F) = e.hom :=
    (congrArg (fun f => e.hom ≫ f) hId).trans (Category.comp_id e.hom)
  have hStart : adj.unit.app A = (adj.homEquiv A F) (𝟙 F) :=
    (adj.homEquiv_id A).symm
  have hOriginal : (adj.homEquiv A F) (𝟙 F) =
      (original.homEquiv A (R.obj F)) (e.hom ≫ R.map (𝟙 F)) :=
    originalAdjunction_homEquiv K n (𝟙 F)
  have hReduce : (original.homEquiv A (R.obj F)) (e.hom ≫ R.map (𝟙 F)) =
      (original.homEquiv A (R.obj F)) e.hom :=
    congrArg (original.homEquiv A (R.obj F)) hMap
  have hUnit : (original.homEquiv A (R.obj F)) e.hom =
      original.unit.app A ≫ (evaluation K n).map e.hom :=
    original.homEquiv_apply A (R.obj F) e.hom
  have hLevel : (evaluation K n).map e.hom = 𝟙 B :=
    spectrumUnitIsoApp_hom_levelMap K X n
  have hLast : original.unit.app A ≫ (evaluation K n).map e.hom =
      original.unit.app A :=
    (congrArg (fun f : B ⟶ B => original.unit.app A ≫ f) hLevel).trans
      (Category.comp_id (original.unit.app A))
  exact hStart.trans (hOriginal.trans (hReduce.trans (hUnit.trans hLast)))

/-- The chosen counit is the original counit under forward presentation and reconstruction. -/
theorem originalAdjunction_counit_app (K : C) (n : ℕ) (F : Carrier K) :
    (enrichedFreeAtEvaluationAdjunction K n).counit.app F =
      (toEnrichedFunctors K).map
        ((freeAtEvaluationAdjunction K n).counit.app ((fromEnrichedFunctors K).obj F)) ≫
        (enrichedCounitIsoApp K F).hom := by
  let A : C := F.toEnrichedFunctor.obj (EnrichedIndex.degree K n)
  let X : SequentialSpectrum C K := (fromEnrichedFunctors K).obj F
  let original : freeAt K n ⊣ evaluation K n := freeAtEvaluationAdjunction K n
  let adj : enrichedFreeAt K n ⊣ (EnrichedFunctorCat.evaluation (V := C)
      (EnrichedIndex.degree K n)) :=
    enrichedFreeAtEvaluationAdjunction K n
  have hStart : adj.counit.app F = (adj.homEquiv A F).symm (𝟙 A) :=
    (adj.homEquiv_symm_id F).symm
  have hOriginal : (adj.homEquiv A F).symm (𝟙 A) =
      (toEnrichedFunctors K).map ((original.homEquiv A X).symm (𝟙 A)) ≫
        (enrichedCounitIsoApp K F).hom :=
    originalAdjunction_homEquiv_symm K n (𝟙 A)
  have hOldCounit : (original.homEquiv A X).symm (𝟙 A) = original.counit.app X :=
    original.homEquiv_symm_id X
  have hLast := congrArg (fun f : (freeAt K n).obj A ⟶ X =>
    (toEnrichedFunctors K).map f ≫ (enrichedCounitIsoApp K F).hom) hOldCounit
  exact hStart.trans (hOriginal.trans hLast)

/-- Whole generator arrows reconstruct with the actual identity-component endpoint isomorphisms. -/
def originalFreeGeneratorIso (K : C) (n : ℕ) {A B : C} (f : A ⟶ B) :
    Arrow.mk ((fromEnrichedFunctors K).map ((enrichedFreeAt K n).map f)) ≅
      Arrow.mk ((freeAt K n).map f) :=
  Arrow.isoMk (spectrumUnitIsoApp K ((freeAt K n).obj A)).symm
    (spectrumUnitIsoApp K ((freeAt K n).obj B)).symm
    (((spectrumUnitIso K).inv.naturality ((freeAt K n).map f)).symm)


variable [∀ r : ℕ, HasCoproductsOfShape (Fin (r + 1)) C]

/-- The lower-degree free-object comparison keeps the entire original selected isomorphism. -/
def enrichedFreeAtLevelIsoOfLt (K : C) {m n : ℕ} (h : m < n) (A : C) :
    ((enrichedFreeAt K n).obj A).toEnrichedFunctor.obj (EnrichedIndex.degree K m) ≅ ⊥_ C := by
  let _ : ∀ X : C, PreservesColimit (Functor.empty.{0} C) (tensorLeft X) :=
    fun X => by infer_instance
  exact freeAtLevelIsoOfLt K h A

/-- The forward-degree free-object comparison keeps the original power, coefficient and maps. -/
def enrichedFreeAtLevelIsoOfLe (K : C) {m n : ℕ} (h : n ≤ m) (A : C) :
    ((enrichedFreeAt K n).obj A).toEnrichedFunctor.obj (EnrichedIndex.degree K m) ≅
      TensorPower.tensorPowObj K (m - n) ⊗ A := by
  let _ : ∀ X : C, PreservesColimit (Functor.empty.{0} C) (tensorLeft X) :=
    fun X => by infer_instance
  exact freeAtLevelIsoOfLe K h A

/-- The lower-degree comparison retains naturality of the actual original coefficient maps. -/
theorem enrichedFreeAtLevelIsoOfLt_hom_naturality (K : C) {m n : ℕ} (h : m < n)
    {A B : C} (f : A ⟶ B) :
    EnrichedFunctorCat.component ((enrichedFreeAt K n).map f) (EnrichedIndex.degree K m) ≫
        (enrichedFreeAtLevelIsoOfLt K h B).hom =
      (enrichedFreeAtLevelIsoOfLt K h A).hom := by
  let _ : ∀ X : C, PreservesColimit (Functor.empty.{0} C) (tensorLeft X) :=
    fun X => by infer_instance
  rw [enrichedFreeAt_map_component]
  exact freeAtLevelIsoOfLt_hom_naturality K h f

/-- The forward comparison retains the original tensor coefficient map. -/
theorem enrichedFreeAtLevelIsoOfLe_hom_naturality (K : C) {m n : ℕ} (h : n ≤ m)
    {A B : C} (f : A ⟶ B) :
    EnrichedFunctorCat.component ((enrichedFreeAt K n).map f) (EnrichedIndex.degree K m) ≫
        (enrichedFreeAtLevelIsoOfLe K h B).hom =
      (enrichedFreeAtLevelIsoOfLe K h A).hom ≫
        (𝟙 (TensorPower.tensorPowObj K (m - n)) ⊗ₘ f) := by
  let _ : ∀ X : C, PreservesColimit (Functor.empty.{0} C) (tensorLeft X) :=
    fun X => by infer_instance
  rw [enrichedFreeAt_map_component]
  exact freeAtLevelIsoOfLe_hom_naturality K h f

end OriginalFreeComparison

end CategoryTheory.SequentialSpectrum.EnrichedPresentation
