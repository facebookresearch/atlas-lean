/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroFiberLocalization
public import MathlibExt.CategoryTheory.Monoidal.CoreRealizedTranslations

/-!
# The split-row inclusion for localized extensions

Construct the split row `A → A ⊞ X → X` and its localized functor. Raw maps
retain the given stabilizer and denominator. The kernel composite is the
identity, and the middle composite is the positive `+[X]` translation with
the literal middle object `A ⊞ X`.

The corresponding natural isomorphisms have the actual identity components
of these composites. The kernel and middle constructions come from
`ZeroFiberLocalization` and `CoreRealizedTranslations`.

These split rows are used in the auxiliary-space construction in Weibel,
*The K-book*, IV.7.1 and IV.7.6.
-/

@[expose] public section

universe u v

open CategoryTheory.MonoidalActionCategory

/-! ## The original split-row inclusion and its two actual projections -/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open CategoryTheory.GenericCoreResidualTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension.SplitInclusion

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] leftSumAction MonoidalActionCategory.diagonalAction

/-- The literal split row at the original, arbitrary given quotient X. -/
def splitRow (X : C) (A : Core C) : FixedTargetExtension C X where
  A := A.of
  B := A.of ⊞ X
  i := biprod.inl
  p := biprod.snd
  zero := by simp
  admissible := by exact isAdmissibleExact_split A.of X

/-- The actual canonical row is admissible in every given exact structure. -/
theorem splitRow_admissible (X : C) (A : Core C) :
    IsAdmissibleExact (splitRow X A).toExtension.row := (splitRow X A).admissible

/-- The middle coordinate is the original inverse associator followed by gamma tensored with X. -/
def splitMiddleIso (X : C) {T A B : Core C} (gamma : T ⊗ A ⟶ B) :
    T.of ⊞ (A.of ⊞ X) ≅ B.of ⊞ X :=
  ((α_ T A (⟨X⟩ : Core C)).inv ≫ gamma ▷ (⟨X⟩ : Core C)).iso

omit [ExactCategory C] in
private theorem right_whisker_hom {T U : Core C} (f : T ⟶ U) (A : Core C) :
    (f ▷ A).iso.hom = biprod.map f.iso.hom (𝟙 A.of) := by
  rewrite [← tensorHom_id, coreBiprodTensorHom_iso_hom]
  rfl

omit [ExactCategory C] in
/-- The middle arrow has the exact A-on-the-left right-positive translation formula. -/
theorem splitMiddleIso_hom (X : C) {T A B : Core C} (gamma : T ⊗ A ⟶ B) :
    (splitMiddleIso X gamma).hom =
      (biprod.associator T.of A.of X).inv ≫ biprod.map gamma.iso.hom (𝟙 X) := by
  have ha : ((α_ T A (⟨X⟩ : Core C)).inv).iso.hom =
      (biprod.associator T.of A.of X).inv := by rfl
  have hg := right_whisker_hom gamma (⟨X⟩ : Core C)
  change ((α_ T A (⟨X⟩ : Core C)).inv).iso.hom ≫
      (gamma ▷ (⟨X⟩ : Core C)).iso.hom =
    (biprod.associator T.of A.of X).inv ≫ biprod.map gamma.iso.hom (𝟙 X)
  exact congrArg₂
    (fun (p : T.of ⊞ (A.of ⊞ X) ⟶ (T.of ⊞ A.of) ⊞ X)
      (q : (T.of ⊞ A.of) ⊞ X ⟶ B.of ⊞ X) => p ≫ q) ha hg

/-- The actual forward iso pair from a stabilized split row to the given target split row. -/
def splitNumeratorMap (X : C) {T A B : Core C} (gamma : T ⊗ A ⟶ B) :
    leftSumObj T (splitRow X A) ⟶ splitRow X B where
  a := gamma.iso
  b := splitMiddleIso X gamma
  comm_i := by
    change biprod.map (𝟙 T.of) (biprod.inl : A.of ⟶ A.of ⊞ X) ≫
        (splitMiddleIso X gamma).hom = gamma.iso.hom ≫
          (biprod.inl : B.of ⟶ B.of ⊞ X)
    have hPrefix :
        biprod.map (𝟙 T.of) (biprod.inl : A.of ⟶ A.of ⊞ X) ≫
          (biprod.associator T.of A.of X).inv =
          (biprod.inl : T.of ⊞ A.of ⟶ (T.of ⊞ A.of) ⊞ X) := by
      apply biprod.hom_ext
      · apply biprod.hom_ext'
        · apply biprod.hom_ext <;> simp [biprod.associator, Category.assoc]
        · apply biprod.hom_ext <;> simp [biprod.associator, Category.assoc]
      · apply biprod.hom_ext' <;> simp [biprod.associator, Category.assoc]
    rw [splitMiddleIso_hom]
    calc
      _ = (biprod.map (𝟙 T.of) (biprod.inl : A.of ⟶ A.of ⊞ X) ≫
          (biprod.associator T.of A.of X).inv) ≫
            biprod.map gamma.iso.hom (𝟙 X) := (Category.assoc _ _ _).symm
      _ = (biprod.inl : T.of ⊞ A.of ⟶ (T.of ⊞ A.of) ⊞ X) ≫
          biprod.map gamma.iso.hom (𝟙 X) :=
        congrArg
          (fun f : T.of ⊞ A.of ⟶ (T.of ⊞ A.of) ⊞ X =>
            f ≫ biprod.map gamma.iso.hom (𝟙 X)) hPrefix
      _ = gamma.iso.hom ≫ (biprod.inl : B.of ⟶ B.of ⊞ X) :=
        biprod.inl_map gamma.iso.hom (𝟙 X)
  comm_p := by
    change (splitMiddleIso X gamma).hom ≫ (biprod.snd : B.of ⊞ X ⟶ X) =
      (biprod.snd : T.of ⊞ (A.of ⊞ X) ⟶ A.of ⊞ X) ≫ biprod.snd
    rw [splitMiddleIso_hom]
    apply biprod.hom_ext'
    · simp [biprod.associator, Category.assoc]
    · apply biprod.hom_ext' <;> simp [biprod.associator, Category.assoc]

/-- The kernel isomorphism is the input numerator, in its original forward direction. -/
theorem splitNumeratorMap_a (X : C) {T A B : Core C} (gamma : T ⊗ A ⟶ B) :
    (splitNumeratorMap X gamma).a = gamma.iso := rfl

/-- The middle isomorphism is the explicit inverse-associator formula. -/
theorem splitNumeratorMap_b (X : C) {T A B : Core C} (gamma : T ⊗ A ⟶ B) :
    (splitNumeratorMap X gamma).b = splitMiddleIso X gamma := rfl

/-- Eta retains the actual denominator and uses the canonical given-X row. -/
def splitLocalizedObject (X : C) (a : SInverse (Core C) (Core C)) :
    localizedRows (C := C) X := ⟨(splitRow X a.of.1, a.of.2)⟩

/-- The kernel object of eta is exactly the input object. -/
theorem splitLocalizedObject_kernel (X : C) (a : SInverse (Core C) (Core C)) :
    kernelLocalizedObject (splitLocalizedObject X a) = a := rfl

/-- The middle object is A tensored with X on the right, at the same denominator. -/
theorem splitLocalizedObject_middle (X : C) (a : SInverse (Core C) (Core C)) :
    middleLocalizedObject (splitLocalizedObject X a) = positiveObj (⟨X⟩ : Core C) a := rfl

/-- The actual raw eta map keeps the original stabilizer and denominator morphism. -/
def splitLocalizedRaw (X : C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (splitLocalizedObject X a) (splitLocalizedObject X b) where
  stabilizer := r.stabilizer
  hom := (splitNumeratorMap X r.hom.1, r.hom.2)

/-- The raw stabilizer has not been reset or replaced. -/
theorem splitLocalizedRaw_stabilizer (X : C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (splitLocalizedRaw X r).stabilizer = r.stabilizer := rfl

/-- The denominator is the original delta, at its original stabilized source. -/
theorem splitLocalizedRaw_denominator (X : C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (splitLocalizedRaw X r).hom.2 = r.hom.2 := rfl

/-- Applying the original kernel projection recovers the complete original raw arrow. -/
theorem splitLocalizedRaw_kernel (X : C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    kernelLocalizedRawMap (splitLocalizedRaw X r) = r := rfl

/-- Applying the original middle projection gives the complete actual right-positive raw arrow. -/
theorem splitLocalizedRaw_middle (X : C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    middleLocalizedRawMap (splitLocalizedRaw X r) = positiveRaw (⟨X⟩ : Core C) r := by
  let x : Core C := ⟨X⟩
  let p := positiveObj x a
  let q := positiveObj x b
  have hh : ((middleLocalizedRawMap (splitLocalizedRaw X r)).hom :
      r.stabilizer ⊙ₗ p.of ⟶ q.of) = (positiveRaw x r).hom := by
    apply Prod.ext
    · rfl
    · exact (positiveRaw_denominator x r).symm
  exact congrArg
    (fun k : r.stabilizer ⊙ₗ p.of ⟶ q.of =>
      (⟨r.stabilizer, k⟩ : MonoidalActionCategory.RawHom p q)) hh


private theorem raw_middle_rel_reflect {X : C} {a b : localizedRows (C := C) X}
    {r s : MonoidalActionCategory.RawHom a b}
    (h : (middleLocalizedRawMap r).Rel (middleLocalizedRawMap s)) : r.Rel s := by
  change ∃ e : r.stabilizer ≅ s.stabilizer,
    e.hom ⊵ₗ (middleLocalizedObject a).of ≫ (middleLocalizedRawMap s).hom =
      (middleLocalizedRawMap r).hom at h
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  apply Prod.ext
  · let k : leftSumObj r.stabilizer a.of.1 ⟶ leftSumObj s.stabilizer a.of.1 :=
      leftSumMap (T := r.stabilizer) (T' := s.stabilizer)
        (F := a.of.1) (G := a.of.1) e.hom (𝟙 a.of.1)
    let f : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := k ≫ s.hom.1
    change f = r.hom.1
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    have hm := congrArg
      (fun q : r.stabilizer ⊙ₗ (middleLocalizedObject a).of ⟶
          (middleLocalizedObject b).of => q.1.iso.hom) he
    change (e.hom ▷ (⟨a.of.1.B⟩ : Core C)).iso.hom ≫ s.hom.1.b.hom =
      r.hom.1.b.hom at hm
    have hk : k.b.hom = biprod.map e.hom.iso.hom (𝟙 a.of.1.B) := by
      simpa only [id_b, Iso.refl_hom] using
        leftSumMap_b_hom (T := r.stabilizer) (T' := s.stabilizer)
          (F := a.of.1) (G := a.of.1) e.hom (𝟙 a.of.1)
    have hc := congrArg Iso.hom (comp_b k s.hom.1)
    change f.b.hom = k.b.hom ≫ s.hom.1.b.hom at hc
    have hf : f.b.hom = biprod.map e.hom.iso.hom (𝟙 a.of.1.B) ≫ s.hom.1.b.hom :=
      hc.trans (congrArg
        (fun p : r.stabilizer.of ⊞ a.of.1.B ⟶ s.stabilizer.of ⊞ a.of.1.B =>
          p ≫ s.hom.1.b.hom) hk)
    have hw := right_whisker_hom e.hom (⟨a.of.1.B⟩ : Core C)
    exact hf.trans ((congrArg
      (fun k : r.stabilizer.of ⊞ a.of.1.B ⟶ s.stabilizer.of ⊞ a.of.1.B =>
        k ≫ s.hom.1.b.hom) hw).symm.trans hm)
  · exact congrArg
      (fun q : r.stabilizer ⊙ₗ (middleLocalizedObject a).of ⟶
          (middleLocalizedObject b).of => q.2) he

private theorem middleHom_injective {X : C} {a b : localizedRows (C := C) X}
    (f g : a ⟶ b) (h : localizedMiddleHomMap f = localizedMiddleHomMap g) : f = g := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  obtain ⟨s, rfl⟩ := MonoidalActionCategory.Hom.exists_rep g
  change MonoidalActionCategory.Hom.mk (middleLocalizedRawMap r) =
    MonoidalActionCategory.Hom.mk (middleLocalizedRawMap s) at h
  exact Quotient.sound (raw_middle_rel_reflect
    ((MonoidalActionCategory.Hom.mk_eq_mk_iff _ _).mp h))

/-- The original stabilizer relation is preserved by the actual split-row maps. -/
theorem splitLocalizedRaw_rel (X : C) {a b : SInverse (Core C) (Core C)}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (splitLocalizedRaw X r).Rel (splitLocalizedRaw X s) := by
  apply raw_middle_rel_reflect
  let x : Core C := ⟨X⟩
  let R := fun p q : MonoidalActionCategory.RawHom (positiveObj x a) (positiveObj x b) =>
    p.Rel q
  have heq : R (middleLocalizedRawMap (splitLocalizedRaw X r))
      (middleLocalizedRawMap (splitLocalizedRaw X s)) = R (positiveRaw x r) (positiveRaw x s) :=
    congrArg₂ R (splitLocalizedRaw_middle X r) (splitLocalizedRaw_middle X s)
  change R (middleLocalizedRawMap (splitLocalizedRaw X r))
    (middleLocalizedRawMap (splitLocalizedRaw X s))
  exact Eq.mp heq.symm (positiveRaw_rel x h)

/-- The denominator-preserving quotient map induced by the proved raw eta construction. -/
def splitLocalizedHomMap (X : C) {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    splitLocalizedObject X a ⟶ splitLocalizedObject X b :=
  Quotient.map (splitLocalizedRaw X) (by
    intro r s h
    exact splitLocalizedRaw_rel X h) f

/-- The actual eta quotient map has exactly the stated raw representative. -/
theorem splitLocalizedHomMap_mk (X : C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    splitLocalizedHomMap X (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (splitLocalizedRaw X r) := rfl

/-- The original kernel projection recovers the actual input morphism class. -/
theorem splitLocalizedHomMap_kernel (X : C) {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    localizedKernelHomMap (splitLocalizedHomMap X f) = f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  change MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap (splitLocalizedRaw X r)) =
    MonoidalActionCategory.Hom.mk r
  exact congrArg MonoidalActionCategory.Hom.mk (splitLocalizedRaw_kernel X r)

/-- The original middle projection is the actual right-positive translation of the input class. -/
theorem splitLocalizedHomMap_middle (X : C) {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    localizedMiddleHomMap (splitLocalizedHomMap X f) = (positiveFunctor (⟨X⟩ : Core C)).map f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  change MonoidalActionCategory.Hom.mk (middleLocalizedRawMap (splitLocalizedRaw X r)) =
    MonoidalActionCategory.Hom.mk (positiveRaw (⟨X⟩ : Core C) r)
  exact congrArg MonoidalActionCategory.Hom.mk (splitLocalizedRaw_middle X r)

/-- Eta_X is constructed from the literal admissible split rows, with no lift witness supplied. -/
def splitLocalizedFunctor (X : C) :
    SInverse (Core C) (Core C) ⥤ localizedRows (C := C) X where
  obj := splitLocalizedObject X
  map {a b} f := splitLocalizedHomMap X f
  map_id a := by
    apply middleHom_injective
    let F := localizedMiddleFunctor X
    let P := positiveFunctor (⟨X⟩ : Core C)
    change F.map (splitLocalizedHomMap X (𝟙 a)) = F.map (𝟙 (splitLocalizedObject X a))
    exact (splitLocalizedHomMap_middle X (𝟙 a)).trans
      ((P.map_id a).trans (F.map_id (splitLocalizedObject X a)).symm)
  map_comp {a b c} f g := by
    apply middleHom_injective
    let F := localizedMiddleFunctor X
    let P := positiveFunctor (⟨X⟩ : Core C)
    let ef := splitLocalizedHomMap X f
    let eg := splitLocalizedHomMap X g
    change F.map (splitLocalizedHomMap X (f ≫ g)) = F.map (ef ≫ eg)
    have hf : F.map ef = P.map f := splitLocalizedHomMap_middle X f
    have hg : F.map eg = P.map g := splitLocalizedHomMap_middle X g
    exact (splitLocalizedHomMap_middle X (f ≫ g)).trans
      ((P.map_comp f g).trans
        ((congrArg₂
          (fun (p : P.obj a ⟶ P.obj b) (q : P.obj b ⟶ P.obj c) => p ≫ q)
          hf.symm hg.symm).trans (F.map_comp ef eg).symm))

/-- The constructed functor keeps the original canonical row and denominator. -/
theorem splitLocalizedFunctor_obj (X : C) (a : SInverse (Core C) (Core C)) :
    (splitLocalizedFunctor X).obj a = splitLocalizedObject X a := rfl

/-- Its map is the original raw T/gamma/delta construction after quotienting. -/
theorem splitLocalizedFunctor_map_mk (X : C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (splitLocalizedFunctor X).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (splitLocalizedRaw X r) := rfl

/-- The actual kernel composite is naturally isomorphic to the identity on the original model. -/
def splitLocalizedKernelIso (X : C) :
    splitLocalizedFunctor X ⋙ localizedKernelFunctor X ≅ 𝟭 (SInverse (Core C) (Core C)) :=
  NatIso.ofComponents (fun a => Iso.refl a) (by
    intro a b f
    change localizedKernelHomMap (splitLocalizedHomMap X f) ≫ 𝟙 b = 𝟙 a ≫ f
    exact (congrArg (fun k : a ⟶ b => k ≫ 𝟙 b) (splitLocalizedHomMap_kernel X f)).trans
      ((Category.comp_id f).trans (Category.id_comp f).symm))

/-- The actual middle composite is naturally isomorphic to right-positive translation by X. -/
def splitLocalizedMiddleIso (X : C) :
    splitLocalizedFunctor X ⋙ localizedMiddleFunctor X ≅ positiveFunctor (⟨X⟩ : Core C) :=
  NatIso.ofComponents (fun a => Iso.refl (positiveObj (⟨X⟩ : Core C) a)) (by
    intro a b f
    let P := positiveFunctor (⟨X⟩ : Core C)
    let pf := P.map f
    change localizedMiddleHomMap (splitLocalizedHomMap X f) ≫ 𝟙 (P.obj b) =
      𝟙 (P.obj a) ≫ pf
    exact (congrArg (fun k : P.obj a ⟶ P.obj b => k ≫ 𝟙 (P.obj b))
      (splitLocalizedHomMap_middle X f)).trans
      ((Category.comp_id pf).trans (Category.id_comp pf).symm))

/-- The kernel comparison component is the actual original pair identity. -/
theorem splitLocalizedKernelIso_hom_app (X : C) (a : SInverse (Core C) (Core C)) :
    (splitLocalizedKernelIso X).hom.app a = 𝟙 a := rfl

/-- The inverse kernel comparison is also the original pair identity. -/
theorem splitLocalizedKernelIso_inv_app (X : C) (a : SInverse (Core C) (Core C)) :
    (splitLocalizedKernelIso X).inv.app a = 𝟙 a := rfl

/-- The middle comparison is the identity at A ⊞ X and the same denominator. -/
theorem splitLocalizedMiddleIso_hom_app (X : C) (a : SInverse (Core C) (Core C)) :
    (splitLocalizedMiddleIso X).hom.app a = 𝟙 (positiveObj (⟨X⟩ : Core C) a) := rfl

/-- The inverse middle comparison retains that very same positive object and denominator. -/
theorem splitLocalizedMiddleIso_inv_app (X : C) (a : SInverse (Core C) (Core C)) :
    (splitLocalizedMiddleIso X).inv.app a = 𝟙 (positiveObj (⟨X⟩ : Core C) a) := rfl

end AlgebraicKTheory.FixedTargetExtension.SplitInclusion

end
