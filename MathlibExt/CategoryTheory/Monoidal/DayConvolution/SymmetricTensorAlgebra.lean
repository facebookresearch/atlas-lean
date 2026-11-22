/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.MonoidLax
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.OrderedTensorAlgebra
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.SymmetricGeneratorWords

/-!
# Symmetric tensor algebras for Day convolution

Symmetric tensor powers form the free commutative Day monoid on a
degree-one generator. The full generator Hom equivalence and adjunction
retain every coefficient map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open scoped MonoidalCategory MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricTensorAlgebra
universe uV vV
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
local notation "idx" => card
open SymmetricGeneratorWords TensorPower
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- The one-letter target concatenation uses the actual left unitor. -/
private theorem tensorPower_add_one_inv (L : V) (n : ℕ) :
    (tensorPowObj_add L n 1).inv = tensorPowObj L n ◁ (λ_ L).hom := by
  apply (cancel_mono (tensorPowObj_add L n 1).hom).mp
  rw [Iso.inv_hom_id, CategoryTheory.Sequence.OrderedTensorAlgebra.tensorPower_add_one_hom]
  change 𝟙 (tensorPowObj L n ⊗ (𝟙_ V ⊗ L)) =
    (tensorPowObj L n ◁ (λ_ L).hom) ≫ (tensorPowObj L n ◁ (λ_ L).inv)
  rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id]

variable [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
attribute [local instance] SymmetricGeneratorWords.powersBraided

/-- The original entire symmetric powers with their actual Day unit, multiplication and symmetry. -/
def freeMonoid (K : V) : CommMon (DayFunctor I V) :=
  { X := DayFunctor.mk (powers K)
    mon := DayFunctor.monObjOfLaxMonoidal (powers K)
    comm := DayFunctor.isCommMonObjOfLaxBraided (powers K) }

/-- The original target Day multiplication gives the complete indexed lax diagram. -/
@[instance_reducible]
def targetLax (M : CommMon (DayFunctor I V)) : M.X.functor.LaxMonoidal :=
  DayFunctor.Monoid.laxMonoidal M.X
attribute [local instance] targetLax

/-- The original target commutativity gives the whole indexed braided diagram. -/
@[instance_reducible]
def targetBraided (M : CommMon (DayFunctor I V)) : M.X.functor.LaxBraided :=
  DayFunctor.Monoid.laxBraided M.X
attribute [local instance] targetBraided

/-- Every complete original generator extends through every original finite coefficient. -/
def fromGenerator (K : V) (M : CommMon (DayFunctor I V))
    (g : K ⟶ M.X.functor.obj (idx 1)) : (freeMonoid K).X ⟶ M.X :=
  SymmetricGeneratorWords.fromGenerator M.X.functor g

/-- Every entire coefficient of the original extension is its whole original word. -/
theorem fromGenerator_app (K : V) (M : CommMon (DayFunctor I V))
    (g : K ⟶ M.X.functor.obj (idx 1)) (n : ℕ) :
    (fromGenerator K M g).natTrans.app (idx n) = word M.X.functor g n := rfl

/-- The actual symmetric source multiplication has its complete original tensor-power coefficient. -/
theorem sourceMultiplication (K : V) (p q : ℕ) :
    (DayFunctor.η (freeMonoid K).X (freeMonoid K).X).app (idx p, idx q) ≫
      μ[(freeMonoid K).X].natTrans.app (idx (p + q)) =
        (TensorPower.tensorPowObj_add K p q).inv :=
  (DayFunctor.monObjOfLaxMonoidal_mul_app (powers K) (idx p) (idx q)).trans
    (powers_pairing K p q)

/-- The original whole Day unit coefficient of the symmetric powers is the identity. -/
theorem sourceUnit (K : V) :
    DayFunctor.ν I V ≫ η[(freeMonoid K).X].natTrans.app (idx 0) = 𝟙 (𝟙_ V) :=
  DayFunctor.monObjOfLaxMonoidal_one_app (powers K)

/-- Every complete indexed target multiplication is its original Day coefficient. -/
theorem targetMultiplication (M : CommMon (DayFunctor I V)) (p q : ℕ) :
    Functor.LaxMonoidal.μ M.X.functor (idx p) (idx q) =
      (DayFunctor.η M.X M.X).app (idx p, idx q) ≫ μ[M.X].natTrans.app (idx (p + q)) := rfl

/-- The whole indexed target unit is the original Day unit coefficient. -/
theorem targetUnit (M : CommMon (DayFunctor I V)) :
    Functor.LaxMonoidal.ε M.X.functor = DayFunctor.ν I V ≫ η[M.X].natTrans.app (idx 0) := rfl

/-- The original degree-one generator extends to the full original symmetric monoid morphism. -/
theorem fromGenerator_isMonHom (K : V) (M : CommMon (DayFunctor I V))
    (g : K ⟶ M.X.functor.obj (idx 1)) : IsMonHom (fromGenerator K M g) := by
  apply DayFunctor.Monoid.isMonHom_of_coefficients (freeMonoid K).X M.X (fromGenerator K M g)
  · change DayFunctor.ν I V ≫ η[(freeMonoid K).X].natTrans.app (idx 0) ≫
        word M.X.functor g 0 = DayFunctor.ν I V ≫ η[M.X].natTrans.app (idx 0)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ word M.X.functor g 0) (sourceUnit K)).trans
        ((Category.id_comp _).trans ((word_zero M.X.functor g).trans (targetUnit M))))
  · rintro ⟨⟨p⟩⟩ ⟨⟨q⟩⟩
    change (DayFunctor.η (freeMonoid K).X (freeMonoid K).X).app (idx p, idx q) ≫
        μ[(freeMonoid K).X].natTrans.app (idx (p + q)) ≫ word M.X.functor g (p + q) =
      (word M.X.functor g p ⊗ₘ word M.X.functor g q) ≫
        (DayFunctor.η M.X M.X).app (idx p, idx q) ≫ μ[M.X].natTrans.app (idx (p + q))
    have hS : (DayFunctor.η (freeMonoid K).X (freeMonoid K).X).app (idx p, idx q) ≫
        μ[(freeMonoid K).X].natTrans.app (idx (p + q)) ≫ word M.X.functor g (p + q) =
      (TensorPower.tensorPowObj_add K p q).inv ≫ word M.X.functor g (p + q) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ word M.X.functor g (p + q)) (sourceMultiplication K p q))
    have hM : (word M.X.functor g p ⊗ₘ word M.X.functor g q) ≫
        Functor.LaxMonoidal.μ M.X.functor (idx p) (idx q) =
      (word M.X.functor g p ⊗ₘ word M.X.functor g q) ≫
        (DayFunctor.η M.X M.X).app (idx p, idx q) ≫ μ[M.X].natTrans.app (idx (p + q)) :=
      congrArg (fun f => (word M.X.functor g p ⊗ₘ word M.X.functor g q) ≫ f)
        (targetMultiplication M p q)
    exact hS.trans ((word_multiplication M.X.functor g p q).trans hM)

/-- The entire original extension is a genuine symmetric commutative-monoid morphism. -/
def fromGeneratorMonoid (K : V) (M : CommMon (DayFunctor I V))
    (g : K ⟶ M.X.functor.obj (idx 1)) : freeMonoid K ⟶ M :=
  CommMon.homMk
    { hom := fromGenerator K M g
      isMonHom_hom := fromGenerator_isMonHom K M g }

/-- The entire extension retrieves the original full degree-one generator. -/
theorem fromGeneratorMonoid_generator (K : V) (M : CommMon (DayFunctor I V))
    (g : K ⟶ M.X.functor.obj (idx 1)) :
    (λ_ K).inv ≫ (fromGeneratorMonoid K M g).hom.hom.natTrans.app (idx 1) = g :=
  word_generator M.X.functor g

/-- Every original monoid map preserves the actual full Day unit coefficient. -/
private theorem monoidHom_unit_coefficient {A M : CommMon (DayFunctor I V)}
    (f : A ⟶ M) :
    DayFunctor.ν I V ≫ η[A.X].natTrans.app (idx 0) ≫ f.hom.hom.natTrans.app (idx 0) =
      DayFunctor.ν I V ≫ η[M.X].natTrans.app (idx 0) := by
  have h := congrArg (fun t : 𝟙_ (DayFunctor I V) ⟶ M.X =>
    t.natTrans.app (idx 0)) (IsMonHom.one_hom f.hom.hom)
  exact congrArg (fun t => DayFunctor.ν I V ≫ t) h

/-- Every original monoid map preserves all actual Day multiplication coefficients. -/
private theorem monoidHom_pair_coefficient {A M : CommMon (DayFunctor I V)}
    (f : A ⟶ M) (a b : I) :
    (DayFunctor.η A.X A.X).app (a, b) ≫ μ[A.X].natTrans.app (a ⊗ b) ≫
      f.hom.hom.natTrans.app (a ⊗ b) =
    (f.hom.hom.natTrans.app a ⊗ₘ f.hom.hom.natTrans.app b) ≫
      (DayFunctor.η M.X M.X).app (a, b) ≫ μ[M.X].natTrans.app (a ⊗ b) := by
  have h := congrArg (fun t : A.X ⊗ A.X ⟶ M.X => t.natTrans.app (a ⊗ b))
    (IsMonHom.mul_hom f.hom.hom)
  have h' := congrArg (fun t => (DayFunctor.η A.X A.X).app (a, b) ≫ t) h
  change (DayFunctor.η A.X A.X).app (a, b) ≫ μ[A.X].natTrans.app (a ⊗ b) ≫
    f.hom.hom.natTrans.app (a ⊗ b) =
    (DayFunctor.η A.X A.X).app (a, b) ≫
      (f.hom.hom ⊗ₘ f.hom.hom).natTrans.app (a ⊗ b) ≫ μ[M.X].natTrans.app (a ⊗ b) at h'
  exact h'.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ μ[M.X].natTrans.app (a ⊗ b))
      (DayFunctor.tensorHom_η f.hom.hom f.hom.hom a b)).trans (Category.assoc _ _ _)))

/-- The full generator of an original symmetric monoid morphism. -/
def generator (K : V) (M : CommMon (DayFunctor I V))
    (f : freeMonoid K ⟶ M) : K ⟶ M.X.functor.obj (idx 1) :=
  (λ_ K).inv ≫ f.hom.hom.natTrans.app (idx 1)

/-- Every coefficient of any original symmetric monoid map is its full generator word. -/
private theorem monoidHom_words (K : V) (M : CommMon (DayFunctor I V))
    (f : freeMonoid K ⟶ M) (n : ℕ) :
    f.hom.hom.natTrans.app (idx n) = word M.X.functor (generator K M f) n := by
  induction n with
  | zero =>
    have h := monoidHom_unit_coefficient f
    have h' := (Category.assoc (DayFunctor.ν I V)
      (η[(freeMonoid K).X].natTrans.app (idx 0))
      (f.hom.hom.natTrans.app (idx 0))).trans h
    change (DayFunctor.ν I V ≫ η[(freeMonoid K).X].natTrans.app (idx 0)) ≫
      f.hom.hom.natTrans.app (idx 0) = LaxMonoidal.ε M.X.functor at h'
    rw [word_zero]
    change f.hom.hom.natTrans.app (idx 0) = LaxMonoidal.ε M.X.functor
    exact (Category.id_comp _).symm.trans
      ((congrArg (fun t => t ≫ f.hom.hom.natTrans.app (idx 0)) (sourceUnit K).symm).trans h')
  | succ n ih =>
    have h := monoidHom_pair_coefficient f (idx n) (idx 1)
    change (DayFunctor.η (freeMonoid K).X (freeMonoid K).X).app (idx n, idx 1) ≫
      μ[(freeMonoid K).X].natTrans.app (idx (n + 1)) ≫
        f.hom.hom.natTrans.app (idx (n + 1)) =
      (f.hom.hom.natTrans.app (idx n) ⊗ₘ f.hom.hom.natTrans.app (idx 1)) ≫
        Functor.LaxMonoidal.μ M.X.functor (idx n) (idx 1) at h
    have h' : (TensorPower.tensorPowObj_add K n 1).inv ≫
        f.hom.hom.natTrans.app (idx (n + 1)) =
      (f.hom.hom.natTrans.app (idx n) ⊗ₘ f.hom.hom.natTrans.app (idx 1)) ≫
        Functor.LaxMonoidal.μ M.X.functor (idx n) (idx 1) := by
      exact (congrArg (fun t => t ≫ f.hom.hom.natTrans.app (idx (n + 1)))
        (sourceMultiplication K n 1).symm).trans ((Category.assoc _ _ _).trans h)
    have h'' := congrArg (fun t => (TensorPower.tensorPowObj_add K n 1).hom ≫ t) h'
    have hs : f.hom.hom.natTrans.app (idx (n + 1)) =
        (TensorPower.tensorPowObj_add K n 1).hom ≫
          (f.hom.hom.natTrans.app (idx n) ⊗ₘ f.hom.hom.natTrans.app (idx 1)) ≫
            Functor.LaxMonoidal.μ M.X.functor (idx n) (idx 1) := by
      have hCancel : (TensorPower.tensorPowObj_add K n 1).hom ≫
          (TensorPower.tensorPowObj_add K n 1).inv ≫ f.hom.hom.natTrans.app (idx (n + 1)) =
        f.hom.hom.natTrans.app (idx (n + 1)) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ f.hom.hom.natTrans.app (idx (n + 1)))
            (TensorPower.tensorPowObj_add K n 1).hom_inv_id).trans (Category.id_comp _))
      exact hCancel.symm.trans h''
    have ht : (TensorPower.tensorPowObj K n ◁ (λ_ K).inv) ≫
        (f.hom.hom.natTrans.app (idx n) ⊗ₘ f.hom.hom.natTrans.app (idx 1)) =
      f.hom.hom.natTrans.app (idx n) ⊗ₘ generator K M f := by
      have h := tensorHom_comp_tensorHom (𝟙 (TensorPower.tensorPowObj K n)) (λ_ K).inv
        (f.hom.hom.natTrans.app (idx n)) (f.hom.hom.natTrans.app (idx 1))
      change ((𝟙 (TensorPower.tensorPowObj K n)) ⊗ₘ (λ_ K).inv) ≫
        (f.hom.hom.natTrans.app (idx n) ⊗ₘ f.hom.hom.natTrans.app (idx 1)) =
        ((𝟙 (TensorPower.tensorPowObj K n)) ≫ f.hom.hom.natTrans.app (idx n)) ⊗ₘ
          generator K M f at h
      exact (congrArg (fun t => t ≫
        (f.hom.hom.natTrans.app (idx n) ⊗ₘ f.hom.hom.natTrans.app (idx 1)))
          (id_tensorHom (TensorPower.tensorPowObj K n) (λ_ K).inv).symm).trans
            (h.trans (congrArg (fun t => t ⊗ₘ generator K M f)
              (Category.id_comp (f.hom.hom.natTrans.app (idx n)))))
    rw [word_successor]
    change f.hom.hom.natTrans.app (idx (n + 1)) =
      (word M.X.functor (generator K M f) n ⊗ₘ generator K M f) ≫
        Functor.LaxMonoidal.μ M.X.functor (idx n) (idx 1)
    exact hs.trans ((congrArg (fun t => t ≫
      (f.hom.hom.natTrans.app (idx n) ⊗ₘ f.hom.hom.natTrans.app (idx 1)) ≫
        Functor.LaxMonoidal.μ M.X.functor (idx n) (idx 1))
        (CategoryTheory.Sequence.OrderedTensorAlgebra.tensorPower_add_one_hom K n)).trans
          (((Category.assoc _ _ _).symm.trans
            (congrArg (fun t => t ≫ Functor.LaxMonoidal.μ M.X.functor (idx n) (idx 1)) ht)).trans
              (congrArg (fun t => (t ⊗ₘ generator K M f) ≫ Functor.LaxMonoidal.μ M.X.functor (idx n) (idx 1)) ih)))

/-- The genuine generator universal property, with both entire original Hom functions. -/
def generatorHomEquiv (K : V) (M : CommMon (DayFunctor I V)) :
    (freeMonoid K ⟶ M) ≃ (K ⟶ M.X.functor.obj (idx 1)) where
  toFun := generator K M
  invFun := fromGeneratorMonoid K M
  left_inv f := by
    apply CommMon.hom_ext
    apply DayFunctor.hom_ext
    apply NatTrans.ext
    funext a
    rcases a with ⟨⟨n⟩⟩
    exact (monoidHom_words K M f n).symm
  right_inv := fromGeneratorMonoid_generator K M

/-- The original generator extension and evaluation recover every full monoid morphism. -/
theorem generatorHomEquiv_left_inv (K : V) (M : CommMon (DayFunctor I V))
    (f : freeMonoid K ⟶ M) :
    fromGeneratorMonoid K M (generator K M f) = f :=
  (generatorHomEquiv K M).left_inv f

/-- The original generator evaluation recovers every original generator arrow. -/
theorem generatorHomEquiv_right_inv (K : V) (M : CommMon (DayFunctor I V))
    (g : K ⟶ M.X.functor.obj (idx 1)) :
    generator K M (fromGeneratorMonoid K M g) = g :=
  (generatorHomEquiv K M).right_inv g

/-- The complete forward generator correspondence is natural in every target monoid map. -/
theorem generatorHomEquiv_natural_target (K : V)
    {M Q : CommMon (DayFunctor I V)} (f : freeMonoid K ⟶ M) (h : M ⟶ Q) :
    generatorHomEquiv K Q (f ≫ h) =
      generatorHomEquiv K M f ≫ h.hom.hom.natTrans.app (idx 1) :=
  (Category.assoc _ _ _).symm

/-- The complete inverse generator correspondence is natural in every target monoid map. -/
theorem generatorHomEquiv_symm_natural_target (K : V)
    {M Q : CommMon (DayFunctor I V)} (g : K ⟶ M.X.functor.obj (idx 1)) (h : M ⟶ Q) :
    (generatorHomEquiv K Q).symm (g ≫ h.hom.hom.natTrans.app (idx 1)) =
      (generatorHomEquiv K M).symm g ≫ h := by
  apply (generatorHomEquiv K Q).injective
  exact ((generatorHomEquiv K Q).apply_symm_apply _).trans
    (((congrArg (fun t => t ≫ h.hom.hom.natTrans.app (idx 1))
      ((generatorHomEquiv K M).apply_symm_apply g)).symm).trans
        (generatorHomEquiv_natural_target K ((generatorHomEquiv K M).symm g) h).symm)


/-- Every original coefficient map induces its complete symmetric free-monoid map. -/
def freeMap {K L : V} (h : K ⟶ L) : freeMonoid K ⟶ freeMonoid L :=
  fromGeneratorMonoid K (freeMonoid L) (h ≫ (λ_ L).inv)

/-- The full free-monoid map has the original degree-one generator. -/
theorem freeMap_generator {K L : V} (h : K ⟶ L) :
    generator K (freeMonoid L) (freeMap h) = h ≫ (λ_ L).inv :=
  fromGeneratorMonoid_generator K (freeMonoid L) (h ≫ (λ_ L).inv)

/-- The complete canonical generator word is the actual tensor-power map. -/
private theorem freeMap_word {K L : V} (f : K ⟶ L) (n : ℕ) :
    word (freeMonoid L).X.functor (f ≫ (λ_ L).inv) n = tensorPowMap f n := by
  induction n with
  | zero =>
    rw [word_zero, targetUnit, sourceUnit]
    rfl
  | succ n ih =>
    rw [word_successor, ih, targetMultiplication, sourceMultiplication,
      tensorPower_add_one_inv, tensorPowMap_succ]
    change (tensorPowMap f n ⊗ₘ (f ≫ (λ_ L).inv)) ≫
      (tensorPowObj L n ◁ (λ_ L).hom) = tensorPowMap f n ⊗ₘ f
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every component of the canonical free-monoid map is its original tensor-power map. -/
theorem freeMap_app {K L : V} (f : K ⟶ L) (A : I) :
    (freeMap f).hom.hom.natTrans.app A = tensorPowMap f A.of.len := by
  rcases A with ⟨⟨n⟩⟩
  change (fromGenerator K (freeMonoid L) (f ≫ (λ_ L).inv)).natTrans.app (card n) = _
  exact (fromGenerator_app K (freeMonoid L) (f ≫ (λ_ L).inv) n).trans (freeMap_word f n)

/-- The entire generator correspondence is natural in every original coefficient arrow. -/
theorem generatorHomEquiv_natural_source {K L : V} (h : K ⟶ L)
    (M : CommMon (DayFunctor I V)) (f : freeMonoid L ⟶ M) :
    generatorHomEquiv K M (freeMap h ≫ f) = h ≫ generatorHomEquiv L M f := by
  have hc := congrArg (fun t => t ≫ f.hom.hom.natTrans.app (idx 1)) (freeMap_generator h)
  exact (Category.assoc (λ_ K).inv ((freeMap h).hom.hom.natTrans.app (idx 1))
    (f.hom.hom.natTrans.app (idx 1))).symm.trans (hc.trans (Category.assoc _ _ _))

/-- The entire inverse generator correspondence is natural in every original coefficient arrow. -/
theorem generatorHomEquiv_symm_natural_source {K L : V} (h : K ⟶ L)
    (M : CommMon (DayFunctor I V)) (g : L ⟶ M.X.functor.obj (idx 1)) :
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

/-- The actual symmetric tensor-power free-monoid functor, with all original coefficient maps. -/
def freeFunctor : V ⥤ CommMon (DayFunctor I V) where
  obj := freeMonoid
  map := freeMap
  map_id := freeMap_id
  map_comp := freeMap_comp

/-- The full original forgetful functor followed by its actual degree-one evaluation. -/
def generatorEvaluation : CommMon (DayFunctor I V) ⥤ V where
  obj M := M.X.functor.obj (idx 1)
  map f := f.hom.hom.natTrans.app (idx 1)

/-- The genuine complete free-generator adjunction for the symmetric tensor-power monoids. -/
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
theorem freeAdjunction_homEquiv (K : V) (M : CommMon (DayFunctor I V)) :
    freeAdjunction.homEquiv K M = generatorHomEquiv K M := by
  unfold freeAdjunction
  exact congrArg (fun e => e K M) (Adjunction.mkOfHomEquiv_homEquiv _)

/-- The actual whole free-adjunction unit is the original degree-one insertion. -/
theorem freeAdjunction_unit (K : V) :
    freeAdjunction.unit.app K = (λ_ K).inv :=
  Category.comp_id (λ_ K).inv

/-- The actual whole free-adjunction counit is the original extension of the identity generator. -/
theorem freeAdjunction_counit (M : CommMon (DayFunctor I V)) :
    freeAdjunction.counit.app M = fromGeneratorMonoid _ M (𝟙 _) := rfl

/-- The complete original free-generator adjunction satisfies its full left triangle. -/
theorem freeAdjunction_left_triangle (K : V) :
    freeFunctor.map (freeAdjunction.unit.app K) ≫
      freeAdjunction.counit.app (freeFunctor.obj K) = 𝟙 (freeFunctor.obj K) :=
  freeAdjunction.left_triangle_components K

/-- The complete original free-generator adjunction satisfies its full right triangle. -/
theorem freeAdjunction_right_triangle (M : CommMon (DayFunctor I V)) :
    freeAdjunction.unit.app (generatorEvaluation.obj M) ≫
      generatorEvaluation.map (freeAdjunction.counit.app M) = 𝟙 (generatorEvaluation.obj M) :=
  freeAdjunction.right_triangle_components M


end CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricTensorAlgebra
