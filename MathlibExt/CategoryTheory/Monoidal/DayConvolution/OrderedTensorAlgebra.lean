/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.MonoidLax
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.OrderedTensorWords
public import MathlibExt.CategoryTheory.Monoidal.Sequence.TensorPower

/-!
# Ordered tensor algebras for Day convolution

Finite ordered tensor powers form the free Day monoid on a degree-one
generator. Both Hom functions, the coefficient maps, and the complete
free-generator adjunction are defined here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open scoped MonoidalCategory MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Sequence.OrderedTensorAlgebra
universe uV vV
local notation "N" => CategoryTheory.Sequence.Index
local notation "idx" => CategoryTheory.Sequence.index
open OrderedTensorWords

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The original ordered tensor-power monoid, with its actual unit and multiplication. -/
def freeMonoid (K : V) : Mon (CategoryTheory.Sequence V) :=
  { X := CategoryTheory.Sequence.tensorPowerSequence K
    mon := CategoryTheory.Sequence.tensorPowerSequenceMonObj K }

/-- The actual Day monoid fields give the original full indexed lax diagram. -/
@[instance_reducible]
def targetLax (M : Mon (CategoryTheory.Sequence V)) : M.X.functor.LaxMonoidal :=
  DayFunctor.Monoid.laxMonoidal M.X

attribute [local instance] targetLax

/-- Every degree of the original generator extension is the full ordered word. -/
def fromGenerator (K : V) (M : Mon (CategoryTheory.Sequence V))
    (g : K ⟶ M.X.functor.obj (idx 1)) : (freeMonoid K).X ⟶ M.X where
  natTrans :=
    { app a := word M.X.functor g (CategoryTheory.Sequence.degree a)
      naturality := by
        intro a b f
        have hab : a = b := Discrete.ext (Discrete.eq_of_hom f)
        subst b
        have hf : f = 𝟙 a := Discrete.hom_eq
        cases hf
        exact (congrArg (fun f => f ≫ word M.X.functor g (CategoryTheory.Sequence.degree a))
          ((freeMonoid K).X.functor.map_id a)).trans
          ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
            (congrArg (fun f => word M.X.functor g (CategoryTheory.Sequence.degree a) ≫ f)
              (M.X.functor.map_id a).symm))) }

/-- The entire component of the original generator extension is its original word. -/
theorem fromGenerator_app (K : V) (M : Mon (CategoryTheory.Sequence V))
    (g : K ⟶ M.X.functor.obj (idx 1)) (n : ℕ) :
    (fromGenerator K M g).natTrans.app (idx n) = word M.X.functor g n := rfl

/-- The actual source tensor-power multiplication has its complete original coefficient map. -/
theorem sourceMultiplication (K : V) (p q : ℕ) :
    (DayFunctor.η (freeMonoid K).X (freeMonoid K).X).app (idx p, idx q) ≫
      μ[(freeMonoid K).X].natTrans.app (idx (p + q)) =
    (TensorPower.tensorPowObj_add K p q).inv := by
  let T := CategoryTheory.Sequence.tensorPowerSequence K
  let m : TensorPower.tensorPowObj K p ⊗ TensorPower.tensorPowObj K q ⟶
      TensorPower.tensorPowObj K (p + q) :=
    (DayFunctor.η T T).app (idx p, idx q) ≫
      (CategoryTheory.Sequence.tensorPowerSequenceMonObj K).mul.natTrans.app (idx (p + q))
  let r : TensorPower.tensorPowObj K (p + q) ⟶ TensorPower.tensorPowObj K (p + q) :=
    T.functor.map (eqToHom (CategoryTheory.Sequence.tensorObj_index p q))
  have hr : r = 𝟙 (TensorPower.tensorPowObj K (p + q)) := by
    change T.functor.map (𝟙 (idx (p + q))) = _
    exact T.functor.map_id _
  have hi : TensorPower.laxTensorPowerPairing (𝟭 V) K p q =
      (TensorPower.tensorPowObj_add K p q).inv := by
    change 𝟙 (TensorPower.tensorPowObj K p ⊗ TensorPower.tensorPowObj K q) ≫
      (TensorPower.tensorPowObj_add K p q).inv = _
    exact Category.id_comp _
  have h := (CategoryTheory.Sequence.tensorPowerSequenceMul_η K p q).trans hi
  have h' := (Category.assoc ((DayFunctor.η T T).app (idx p, idx q))
    ((CategoryTheory.Sequence.tensorPowerSequenceMonObj K).mul.natTrans.app (idx (p + q)))
    (T.functor.map (eqToHom (CategoryTheory.Sequence.tensorObj_index p q)))).trans h
  change m ≫ r = (TensorPower.tensorPowObj_add K p q).inv at h'
  change m = _
  exact (Category.comp_id m).symm.trans ((congrArg (fun f => m ≫ f) hr.symm).trans h')

/-- The original full Day unit coefficient of the ordered tensor-power monoid is the identity. -/
theorem sourceUnit (K : V) :
    DayFunctor.ν N V ≫ η[(freeMonoid K).X].natTrans.app (idx 0) = 𝟙 (𝟙_ V) :=
  CategoryTheory.Sequence.tensorPowerSequenceOne_ν K

/-- The complete original indexed target multiplication is the actual Day coefficient. -/
theorem targetMultiplication (M : Mon (CategoryTheory.Sequence V)) (p q : ℕ) :
    pairing M.X.functor p q =
      (DayFunctor.η M.X M.X).app (idx p, idx q) ≫ μ[M.X].natTrans.app (idx (p + q)) := rfl

/-- The original indexed target unit is the actual Day unit coefficient. -/
theorem targetUnit (M : Mon (CategoryTheory.Sequence V)) :
    LaxMonoidal.ε M.X.functor = DayFunctor.ν N V ≫ η[M.X].natTrans.app (idx 0) := rfl

/-- The original degree-one generator extends to the entire ordered monoid morphism. -/
theorem fromGenerator_isMonHom (K : V) (M : Mon (CategoryTheory.Sequence V))
    (g : K ⟶ M.X.functor.obj (idx 1)) : IsMonHom (fromGenerator K M g) := by
  apply DayFunctor.Monoid.isMonHom_of_coefficients (freeMonoid K).X M.X (fromGenerator K M g)
  · change DayFunctor.ν N V ≫ η[(freeMonoid K).X].natTrans.app (idx 0) ≫
        word M.X.functor g 0 = DayFunctor.ν N V ≫ η[M.X].natTrans.app (idx 0)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ word M.X.functor g 0) (sourceUnit K)).trans
        ((Category.id_comp _).trans (targetUnit M)))
  · intro a b
    obtain ⟨p, rfl⟩ := (show ∃ p : ℕ, idx p = a from ⟨CategoryTheory.Sequence.degree a, rfl⟩)
    obtain ⟨q, rfl⟩ := (show ∃ q : ℕ, idx q = b from ⟨CategoryTheory.Sequence.degree b, rfl⟩)
    change (DayFunctor.η (freeMonoid K).X (freeMonoid K).X).app (idx p, idx q) ≫
        μ[(freeMonoid K).X].natTrans.app (idx (p + q)) ≫ word M.X.functor g (p + q) =
      (word M.X.functor g p ⊗ₘ word M.X.functor g q) ≫
        (DayFunctor.η M.X M.X).app (idx p, idx q) ≫ μ[M.X].natTrans.app (idx (p + q))
    calc
      _ = (TensorPower.tensorPowObj_add K p q).inv ≫ word M.X.functor g (p + q) :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ word M.X.functor g (p + q)) (sourceMultiplication K p q))
      _ = (word M.X.functor g p ⊗ₘ word M.X.functor g q) ≫ pairing M.X.functor p q :=
        (word_pairing M.X.functor g p q).symm
      _ = _ := (congrArg (fun f => (word M.X.functor g p ⊗ₘ word M.X.functor g q) ≫ f)
        (targetMultiplication M p q))

/-- The whole original extension, bundled as an actual monoid morphism. -/
def fromGeneratorMonoid (K : V) (M : Mon (CategoryTheory.Sequence V))
    (g : K ⟶ M.X.functor.obj (idx 1)) : freeMonoid K ⟶ M :=
  { hom := fromGenerator K M g
    isMonHom_hom := fromGenerator_isMonHom K M g }

/-- The complete original extension retrieves its entire degree-one generator. -/
theorem fromGeneratorMonoid_generator (K : V) (M : Mon (CategoryTheory.Sequence V))
    (g : K ⟶ M.X.functor.obj (idx 1)) :
    (λ_ K).inv ≫ (fromGeneratorMonoid K M g).hom.natTrans.app (idx 1) = g :=
  word_one_generator M.X.functor g

end CategoryTheory.Sequence.OrderedTensorAlgebra


namespace CategoryTheory.Sequence.OrderedTensorAlgebra
universe uV vV
local notation "N" => CategoryTheory.Sequence.Index
local notation "idx" => CategoryTheory.Sequence.index
open OrderedTensorWords

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- The original one-factor concatenation is the inverse left unitor on that factor. -/
theorem tensorPower_add_one_hom (K : V) (n : ℕ) :
    (TensorPower.tensorPowObj_add K n 1).hom =
      TensorPower.tensorPowObj K n ◁ (λ_ K).inv := by
  change ((ρ_ (TensorPower.tensorPowObj K n)).inv ⊗ₘ 𝟙 K) ≫
    (α_ (TensorPower.tensorPowObj K n) (𝟙_ V) K).hom = _
  exact (congrArg (fun f => f ≫
    (α_ (TensorPower.tensorPowObj K n) (𝟙_ V) K).hom)
      (tensorHom_id (ρ_ (TensorPower.tensorPowObj K n)).inv K)).trans
        (triangle_assoc_comp_right_inv (TensorPower.tensorPowObj K n) K)

variable [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

attribute [local instance] targetLax

/-- Every original monoid map preserves the actual full Day unit coefficient. -/
private theorem monoidHom_unit_coefficient {A M : Mon (CategoryTheory.Sequence V)}
    (f : A ⟶ M) :
    DayFunctor.ν N V ≫ η[A.X].natTrans.app (idx 0) ≫ f.hom.natTrans.app (idx 0) =
      DayFunctor.ν N V ≫ η[M.X].natTrans.app (idx 0) := by
  have h := congrArg (fun t : 𝟙_ (CategoryTheory.Sequence V) ⟶ M.X =>
    t.natTrans.app (idx 0)) (IsMonHom.one_hom f.hom)
  exact congrArg (fun t => DayFunctor.ν N V ≫ t) h

/-- Every original monoid map preserves all actual Day multiplication coefficients. -/
private theorem monoidHom_pair_coefficient {A M : Mon (CategoryTheory.Sequence V)}
    (f : A ⟶ M) (a b : N) :
    (DayFunctor.η A.X A.X).app (a, b) ≫ μ[A.X].natTrans.app (a ⊗ b) ≫
      f.hom.natTrans.app (a ⊗ b) =
    (f.hom.natTrans.app a ⊗ₘ f.hom.natTrans.app b) ≫
      (DayFunctor.η M.X M.X).app (a, b) ≫ μ[M.X].natTrans.app (a ⊗ b) := by
  have h := congrArg (fun t : A.X ⊗ A.X ⟶ M.X => t.natTrans.app (a ⊗ b))
    (IsMonHom.mul_hom f.hom)
  have h' := congrArg (fun t => (DayFunctor.η A.X A.X).app (a, b) ≫ t) h
  change (DayFunctor.η A.X A.X).app (a, b) ≫ μ[A.X].natTrans.app (a ⊗ b) ≫
    f.hom.natTrans.app (a ⊗ b) =
    (DayFunctor.η A.X A.X).app (a, b) ≫
      (f.hom ⊗ₘ f.hom).natTrans.app (a ⊗ b) ≫ μ[M.X].natTrans.app (a ⊗ b) at h'
  exact h'.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ μ[M.X].natTrans.app (a ⊗ b))
      (DayFunctor.tensorHom_η f.hom f.hom a b)).trans (Category.assoc _ _ _)))

/-- The full generator of an original ordered monoid morphism. -/
def generator (K : V) (M : Mon (CategoryTheory.Sequence V))
    (f : freeMonoid K ⟶ M) : K ⟶ M.X.functor.obj (idx 1) :=
  (λ_ K).inv ≫ f.hom.natTrans.app (idx 1)

/-- Every coefficient of any original ordered monoid map is its full generator word. -/
private theorem monoidHom_words (K : V) (M : Mon (CategoryTheory.Sequence V))
    (f : freeMonoid K ⟶ M) (n : ℕ) :
    f.hom.natTrans.app (idx n) = word M.X.functor (generator K M f) n := by
  induction n with
  | zero =>
    have h := monoidHom_unit_coefficient f
    have h' := (Category.assoc (DayFunctor.ν N V)
      (η[(freeMonoid K).X].natTrans.app (idx 0))
      (f.hom.natTrans.app (idx 0))).trans h
    change (DayFunctor.ν N V ≫ η[(freeMonoid K).X].natTrans.app (idx 0)) ≫
      f.hom.natTrans.app (idx 0) = LaxMonoidal.ε M.X.functor at h'
    change f.hom.natTrans.app (idx 0) = LaxMonoidal.ε M.X.functor
    exact (Category.id_comp _).symm.trans
      ((congrArg (fun t => t ≫ f.hom.natTrans.app (idx 0)) (sourceUnit K).symm).trans h')
  | succ n ih =>
    have h := monoidHom_pair_coefficient f (idx n) (idx 1)
    change (DayFunctor.η (freeMonoid K).X (freeMonoid K).X).app (idx n, idx 1) ≫
      μ[(freeMonoid K).X].natTrans.app (idx (n + 1)) ≫
        f.hom.natTrans.app (idx (n + 1)) =
      (f.hom.natTrans.app (idx n) ⊗ₘ f.hom.natTrans.app (idx 1)) ≫
        pairing M.X.functor n 1 at h
    have h' : (TensorPower.tensorPowObj_add K n 1).inv ≫
        f.hom.natTrans.app (idx (n + 1)) =
      (f.hom.natTrans.app (idx n) ⊗ₘ f.hom.natTrans.app (idx 1)) ≫
        pairing M.X.functor n 1 := by
      calc
        _ = ((DayFunctor.η (freeMonoid K).X (freeMonoid K).X).app (idx n, idx 1) ≫
            μ[(freeMonoid K).X].natTrans.app (idx (n + 1))) ≫
              f.hom.natTrans.app (idx (n + 1)) :=
          congrArg (fun t => t ≫ f.hom.natTrans.app (idx (n + 1)))
            (sourceMultiplication K n 1).symm
        _ = _ := (Category.assoc _ _ _).trans h
    have h'' := congrArg (fun t => (TensorPower.tensorPowObj_add K n 1).hom ≫ t) h'
    have hs : f.hom.natTrans.app (idx (n + 1)) =
        (TensorPower.tensorPowObj_add K n 1).hom ≫
          (f.hom.natTrans.app (idx n) ⊗ₘ f.hom.natTrans.app (idx 1)) ≫
            pairing M.X.functor n 1 := by
      have hCancel : (TensorPower.tensorPowObj_add K n 1).hom ≫
          (TensorPower.tensorPowObj_add K n 1).inv ≫ f.hom.natTrans.app (idx (n + 1)) =
        f.hom.natTrans.app (idx (n + 1)) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ f.hom.natTrans.app (idx (n + 1)))
            (TensorPower.tensorPowObj_add K n 1).hom_inv_id).trans (Category.id_comp _))
      exact hCancel.symm.trans h''
    have ht : (TensorPower.tensorPowObj K n ◁ (λ_ K).inv) ≫
        (f.hom.natTrans.app (idx n) ⊗ₘ f.hom.natTrans.app (idx 1)) =
      f.hom.natTrans.app (idx n) ⊗ₘ generator K M f := by
      have h := tensorHom_comp_tensorHom (𝟙 (TensorPower.tensorPowObj K n)) (λ_ K).inv
        (f.hom.natTrans.app (idx n)) (f.hom.natTrans.app (idx 1))
      change ((𝟙 (TensorPower.tensorPowObj K n)) ⊗ₘ (λ_ K).inv) ≫
        (f.hom.natTrans.app (idx n) ⊗ₘ f.hom.natTrans.app (idx 1)) =
        ((𝟙 (TensorPower.tensorPowObj K n)) ≫ f.hom.natTrans.app (idx n)) ⊗ₘ
          generator K M f at h
      exact (congrArg (fun t => t ≫
        (f.hom.natTrans.app (idx n) ⊗ₘ f.hom.natTrans.app (idx 1)))
          (id_tensorHom (TensorPower.tensorPowObj K n) (λ_ K).inv).symm).trans
            (h.trans (congrArg (fun t => t ⊗ₘ generator K M f)
              (Category.id_comp (f.hom.natTrans.app (idx n)))))
    change f.hom.natTrans.app (idx (n + 1)) =
      (word M.X.functor (generator K M f) n ⊗ₘ generator K M f) ≫
        pairing M.X.functor n 1
    exact hs.trans ((congrArg (fun t => t ≫
      (f.hom.natTrans.app (idx n) ⊗ₘ f.hom.natTrans.app (idx 1)) ≫
        pairing M.X.functor n 1) (tensorPower_add_one_hom K n)).trans
          (((Category.assoc _ _ _).symm.trans
            (congrArg (fun t => t ≫ pairing M.X.functor n 1) ht)).trans
              (congrArg (fun t => (t ⊗ₘ generator K M f) ≫ pairing M.X.functor n 1) ih)))

/-- The genuine generator universal property, with both entire original Hom functions. -/
def generatorHomEquiv (K : V) (M : Mon (CategoryTheory.Sequence V)) :
    (freeMonoid K ⟶ M) ≃ (K ⟶ M.X.functor.obj (idx 1)) where
  toFun := generator K M
  invFun := fromGeneratorMonoid K M
  left_inv f := by
    apply Mon.Hom.ext
    apply DayFunctor.hom_ext
    apply NatTrans.ext
    funext a
    exact (monoidHom_words K M f (CategoryTheory.Sequence.degree a)).symm
  right_inv := fromGeneratorMonoid_generator K M

/-- The original generator extension and evaluation recover every full monoid morphism. -/
theorem generatorHomEquiv_left_inv (K : V) (M : Mon (CategoryTheory.Sequence V))
    (f : freeMonoid K ⟶ M) :
    fromGeneratorMonoid K M (generator K M f) = f :=
  (generatorHomEquiv K M).left_inv f

/-- The original generator evaluation recovers every original generator arrow. -/
theorem generatorHomEquiv_right_inv (K : V) (M : Mon (CategoryTheory.Sequence V))
    (g : K ⟶ M.X.functor.obj (idx 1)) :
    generator K M (fromGeneratorMonoid K M g) = g :=
  (generatorHomEquiv K M).right_inv g

/-- The complete forward generator correspondence is natural in every target monoid map. -/
theorem generatorHomEquiv_natural_target (K : V)
    {M Q : Mon (CategoryTheory.Sequence V)} (f : freeMonoid K ⟶ M) (h : M ⟶ Q) :
    generatorHomEquiv K Q (f ≫ h) =
      generatorHomEquiv K M f ≫ h.hom.natTrans.app (idx 1) :=
  (Category.assoc _ _ _).symm

/-- The complete inverse generator correspondence is natural in every target monoid map. -/
theorem generatorHomEquiv_symm_natural_target (K : V)
    {M Q : Mon (CategoryTheory.Sequence V)} (g : K ⟶ M.X.functor.obj (idx 1)) (h : M ⟶ Q) :
    (generatorHomEquiv K Q).symm (g ≫ h.hom.natTrans.app (idx 1)) =
      (generatorHomEquiv K M).symm g ≫ h := by
  apply (generatorHomEquiv K Q).injective
  exact ((generatorHomEquiv K Q).apply_symm_apply _).trans
    (((congrArg (fun t => t ≫ h.hom.natTrans.app (idx 1))
      ((generatorHomEquiv K M).apply_symm_apply g)).symm).trans
        (generatorHomEquiv_natural_target K ((generatorHomEquiv K M).symm g) h).symm)

end CategoryTheory.Sequence.OrderedTensorAlgebra


namespace CategoryTheory.Sequence.OrderedTensorAlgebra
universe uV vV
local notation "N" => CategoryTheory.Sequence.Index
local notation "idx" => CategoryTheory.Sequence.index
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Every original coefficient map induces its complete ordered free-monoid map. -/
def freeMap {K L : V} (h : K ⟶ L) : freeMonoid K ⟶ freeMonoid L :=
  fromGeneratorMonoid K (freeMonoid L) (h ≫ (λ_ L).inv)

/-- The full free-monoid map has the original degree-one generator. -/
theorem freeMap_generator {K L : V} (h : K ⟶ L) :
    generator K (freeMonoid L) (freeMap h) = h ≫ (λ_ L).inv :=
  fromGeneratorMonoid_generator K (freeMonoid L) (h ≫ (λ_ L).inv)

/-- The entire generator correspondence is natural in every original coefficient arrow. -/
theorem generatorHomEquiv_natural_source {K L : V} (h : K ⟶ L)
    (M : Mon (CategoryTheory.Sequence V)) (f : freeMonoid L ⟶ M) :
    generatorHomEquiv K M (freeMap h ≫ f) = h ≫ generatorHomEquiv L M f := by
  have hc := congrArg (fun t => t ≫ f.hom.natTrans.app (idx 1)) (freeMap_generator h)
  exact (Category.assoc (λ_ K).inv ((freeMap h).hom.natTrans.app (idx 1))
    (f.hom.natTrans.app (idx 1))).symm.trans (hc.trans (Category.assoc _ _ _))

/-- The entire inverse generator correspondence is natural in every original coefficient arrow. -/
theorem generatorHomEquiv_symm_natural_source {K L : V} (h : K ⟶ L)
    (M : Mon (CategoryTheory.Sequence V)) (g : L ⟶ M.X.functor.obj (idx 1)) :
    (generatorHomEquiv K M).symm (h ≫ g) =
      freeMap h ≫ (generatorHomEquiv L M).symm g := by
  apply (generatorHomEquiv K M).injective
  exact ((generatorHomEquiv K M).apply_symm_apply _).trans
    (((congrArg (fun t => h ≫ t) ((generatorHomEquiv L M).apply_symm_apply g)).symm).trans
      (generatorHomEquiv_natural_source h M ((generatorHomEquiv L M).symm g)).symm)

/-- The complete free-monoid construction preserves every original identity map. -/
theorem freeMap_id (K : V) : freeMap (𝟙 K) = 𝟙 (freeMonoid K) := by
  apply (generatorHomEquiv K (freeMonoid K)).injective
  change generator K (freeMonoid K) (freeMap (𝟙 K)) =
    (λ_ K).inv ≫ 𝟙 (TensorPower.tensorPowObj K 1)
  exact (freeMap_generator (𝟙 K)).trans
    ((Category.id_comp (λ_ K).inv).trans (Category.comp_id (λ_ K).inv).symm)

/-- The complete free-monoid construction preserves every original composite map. -/
theorem freeMap_comp {K L P : V} (h : K ⟶ L) (k : L ⟶ P) :
    freeMap (h ≫ k) = freeMap h ≫ freeMap k := by
  apply (generatorHomEquiv K (freeMonoid P)).injective
  have hr := (generatorHomEquiv_natural_source h (freeMonoid P) (freeMap k)).trans
    (congrArg (fun t => h ≫ t) (freeMap_generator k))
  exact (freeMap_generator (h ≫ k)).trans ((Category.assoc _ _ _).trans hr.symm)

/-- The actual ordered tensor-power free-monoid functor, with all original coefficient maps. -/
def freeFunctor : V ⥤ Mon (CategoryTheory.Sequence V) where
  obj := freeMonoid
  map := freeMap
  map_id := freeMap_id
  map_comp := freeMap_comp

/-- The full original forgetful functor followed by its actual degree-one evaluation. -/
def generatorEvaluation : Mon (CategoryTheory.Sequence V) ⥤ V :=
  Mon.forget (CategoryTheory.Sequence V) ⋙ CategoryTheory.Sequence.evaluation V 1

/-- The genuine complete free-generator adjunction for the ordered tensor-power monoids. -/
def freeAdjunction : freeFunctor (V := V) ⊣ generatorEvaluation (V := V) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := generatorHomEquiv
      homEquiv_naturality_left_symm := by
        intro K L M h g
        exact generatorHomEquiv_symm_natural_source h M g
      homEquiv_naturality_right := by
        intro K M Q f g
        exact generatorHomEquiv_natural_target K f g }

/-- Both Hom functions of the full free adjunction are exactly the original generator functions. -/
theorem freeAdjunction_homEquiv (K : V) (M : Mon (CategoryTheory.Sequence V)) :
    freeAdjunction.homEquiv K M = generatorHomEquiv K M := by
  unfold freeAdjunction
  exact congrArg (fun e => e K M) (Adjunction.mkOfHomEquiv_homEquiv _)

/-- The actual whole free-adjunction unit is the original degree-one insertion. -/
theorem freeAdjunction_unit (K : V) :
    freeAdjunction.unit.app K = (λ_ K).inv :=
  Category.comp_id (λ_ K).inv

/-- The actual whole free-adjunction counit is the original extension of the identity generator. -/
theorem freeAdjunction_counit (M : Mon (CategoryTheory.Sequence V)) :
    freeAdjunction.counit.app M = fromGeneratorMonoid _ M (𝟙 _) := rfl

/-- The complete original free-generator adjunction satisfies its full left triangle. -/
theorem freeAdjunction_left_triangle (K : V) :
    freeFunctor.map (freeAdjunction.unit.app K) ≫
      freeAdjunction.counit.app (freeFunctor.obj K) = 𝟙 (freeFunctor.obj K) :=
  freeAdjunction.left_triangle_components K

/-- The complete original free-generator adjunction satisfies its full right triangle. -/
theorem freeAdjunction_right_triangle (M : Mon (CategoryTheory.Sequence V)) :
    freeAdjunction.unit.app (generatorEvaluation.obj M) ≫
      generatorEvaluation.map (freeAdjunction.counit.app M) = 𝟙 (generatorEvaluation.obj M) :=
  freeAdjunction.right_triangle_components M

end CategoryTheory.Sequence.OrderedTensorAlgebra


namespace CategoryTheory.Sequence.OrderedTensorAlgebra

universe uV vV
local notation "N" => CategoryTheory.Sequence.Index
local notation "idx" => CategoryTheory.Sequence.index
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- The full original one-factor inverse concatenation is the left unitor on that factor. -/
theorem tensorPower_add_one_inv (K : V) (n : ℕ) :
    (TensorPower.tensorPowObj_add K n 1).inv =
      TensorPower.tensorPowObj K n ◁ (λ_ K).hom := by
  change (α_ (TensorPower.tensorPowObj K n) (𝟙_ V) K).inv ≫
    ((ρ_ (TensorPower.tensorPowObj K n)).hom ⊗ₘ 𝟙 K) = _
  exact (congrArg (fun t =>
    (α_ (TensorPower.tensorPowObj K n) (𝟙_ V) K).inv ≫ t)
      (tensorHom_id (ρ_ (TensorPower.tensorPowObj K n)).hom K)).trans
        (triangle_assoc_comp_right (TensorPower.tensorPowObj K n) K)

variable [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

attribute [local instance] targetLax
open OrderedTensorWords

/-- Every original coefficient of a free-monoid map is the full original finite tensor-power map. -/
theorem freeMap_app {K L : V} (h : K ⟶ L) (n : ℕ) :
    (freeMap h).hom.natTrans.app (idx n) = TensorPower.tensorPowMap h n := by
  change word (freeMonoid L).X.functor (h ≫ (λ_ L).inv) n = TensorPower.tensorPowMap h n
  induction n with
  | zero => exact sourceUnit L
  | succ n ih =>
    let w : TensorPower.tensorPowObj K n ⟶ TensorPower.tensorPowObj L n :=
      word (freeMonoid L).X.functor (h ≫ (λ_ L).inv) n
    let T : V := TensorPower.tensorPowObj L n
    have hPair : pairing (freeMonoid L).X.functor n 1 = T ◁ (λ_ L).hom :=
      (targetMultiplication (freeMonoid L) n 1).trans
        ((sourceMultiplication L n 1).trans (tensorPower_add_one_inv L n))
    have hSplit : (w ⊗ₘ (h ≫ (λ_ L).inv)) = (w ⊗ₘ h) ≫ (T ◁ (λ_ L).inv) := by
      have h₀ := tensorHom_comp_tensorHom w h (𝟙 T) (λ_ L).inv
      have h₁ := h₀.trans (congrArg (fun t => t ⊗ₘ (h ≫ (λ_ L).inv)) (Category.comp_id w))
      exact h₁.symm.trans
        (congrArg (fun t => (w ⊗ₘ h) ≫ t) (id_tensorHom T (λ_ L).inv))
    have hCancel : (T ◁ (λ_ L).inv) ≫ (T ◁ (λ_ L).hom) = 𝟙 (T ⊗ L) :=
      (MonoidalCategory.whiskerLeft_comp T (λ_ L).inv (λ_ L).hom).symm.trans
        ((congrArg (fun t => T ◁ t) (λ_ L).inv_hom_id).trans (MonoidalCategory.whiskerLeft_id T L))
    change (w ⊗ₘ (h ≫ (λ_ L).inv)) ≫ pairing (freeMonoid L).X.functor n 1 =
      TensorPower.tensorPowMap h n ⊗ₘ h
    let m : T ⊗ (𝟙_ V ⊗ L) ⟶ T ⊗ L := pairing (freeMonoid L).X.functor n 1
    have hm : m = T ◁ (λ_ L).hom := hPair
    change (w ⊗ₘ (h ≫ (λ_ L).inv)) ≫ m = TensorPower.tensorPowMap h n ⊗ₘ h
    exact ((congrArg (fun t => t ≫ m) hSplit).trans (Category.assoc _ _ _)).trans
      ((congrArg (fun t => (w ⊗ₘ h) ≫ (T ◁ (λ_ L).inv) ≫ t) hm).trans
        ((congrArg (fun t => (w ⊗ₘ h) ≫ t) hCancel).trans
          ((Category.comp_id (w ⊗ₘ h)).trans (congrArg (fun t => t ⊗ₘ h) ih))))

end CategoryTheory.Sequence.OrderedTensorAlgebra
