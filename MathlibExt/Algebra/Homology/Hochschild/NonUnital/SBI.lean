/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic
public import MathlibExt.Algebra.Homology.PartialTotalCokernel
public import MathlibExt.Algebra.Homology.PartialTotalCoordinates
public import MathlibExt.Algebra.Homology.PartialTotalEvenTail
public import MathlibExt.Algebra.Homology.ConnesSBI
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# The SBI sequence of the two-column cyclic presentation

Let `k` be a commutative ring and `A` a nonunital ring with a compatible `k`-module structure.
The cyclic bicomplex alternates its `b` and `b′` columns and its horizontal maps `1-t` and
`N`. Let `CC(A)` be its total and `CC^{(2)}(A)` the total of columns zero and one.

The short exact sequence `0 → CC^{(2)}(A) → CC(A) → Q(A) → 0`, together with the period-two
comparison of `Q(A)` with the degree-two extension of `CC(A)`, gives an exact SBI diagram. Its
ordinary term is `H_n(CC^{(2)}(A))`; the maps are `I_n : H_n(CC^{(2)}) → HC_n`, `S_n :
HC_(n+2) → HC_n`, and `B_n : HC_n → H_(n+1)(CC^{(2)})`. All maps are natural for nonunital
algebra homomorphisms. The tail vanishes below degree two, giving an isomorphism for `I_0` and
an epimorphism for `I_1`.

References: Loday, *Cyclic Homology*, Sections 1.4.1 and 1.4.5, Theorem 2.2.1, and Corollary
2.2.3.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits HomologicalComplex HomologicalComplex₂
open ModuleCat.Algebra.Hochschild.NonUnital
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild

/-- Parity after translation by two columns.

For `p ∈ ℕ`, the column indices `p+2` and `p` have the same parity. -/
theorem cyclicColumn_two_parity (p : ℕ) : Even (p + 2) ↔ Even p := by
  rw [show p + 2 = (p + 1) + 1 by omega, Nat.even_add_one, Nat.even_add_one,
    not_not]

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The total of the first two cyclic bicomplex columns.

For a nonunital ground algebra `A`, this chain complex retains outer columns zero and one of
the cyclic bicomplex, including both the `b` and `b′` columns. -/
abbrev cyclicFirstTwoColumns : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (cyclicBicomplex k A).partialTotal 1

/-- The cyclic-total quotient by its first two columns.

This is the cokernel of the chain inclusion of the first-two-column total into the full cyclic
total. -/
abbrev cyclicTwoColumnTail : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  cokernel ((cyclicBicomplex k A).partialTotalι 1)

/-- The inclusion-and-quotient sequence for two cyclic columns.

The short complex has first term the first-two-column total, middle term the full cyclic
total, and third term the cokernel of their inclusion. -/
abbrev cyclicTwoColumnSequence : ShortComplex (ChainComplex (ModuleCat.{max u v} k) ℕ) :=
  (cyclicBicomplex k A).partialTotalCokernelShortComplex 1

/-- The cyclic total as the middle term of the two-column sequence.

The middle chain complex of the inclusion-and-quotient sequence is the full cyclic total
`CC(A)`. -/
lemma cyclicTwoColumnSequence_X₂ :
    (cyclicTwoColumnSequence k A).X₂ = cyclicTotal k A := rfl

/-- The retained-column term of the cyclic short complex.

The first term of the inclusion-and-quotient sequence is the total `CC^{(2)}(A)` of outer
columns zero and one. -/
lemma cyclicTwoColumnSequence_X₁ :
    (cyclicTwoColumnSequence k A).X₁ = cyclicFirstTwoColumns k A := rfl

/-- The cokernel term of the cyclic short complex.

The third term of the two-column sequence is the quotient of `CC(A)` by the retained first-
two-column total. -/
lemma cyclicTwoColumnSequence_X₃ :
    (cyclicTwoColumnSequence k A).X₃ = cyclicTwoColumnTail k A := rfl

/-- Short exactness of the cyclic two-column sequence.

The inclusion of `CC^{(2)}(A)` into `CC(A)` and its cokernel form a short exact sequence of
chain complexes. -/
theorem cyclicTwoColumnSequence_shortExact :
    (cyclicTwoColumnSequence k A).ShortExact :=
  (cyclicBicomplex k A).partialTotalCokernelShortExact 1

/-- A cell inclusion in the first-two-column cyclic total.

For `p : Fin 2` and `p+q=n`, this includes the coefficient tensor cell in bidegree `(p,q)`
into degree `n` of `CC^{(2)}(A)`. -/
def cyclicFirstTwoColumnCell (p : Fin 2) (q n : ℕ) (h : p.val + q = n) :
    ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q ⟶ (cyclicFirstTwoColumns k A).X n :=
  (cyclicBicomplex k A).partialTotalComponent 1 p q n h

/-- The full-total image of a retained cyclic cell.

A cell inclusion into `CC^{(2)}(A)` followed by its inclusion into `CC(A)` is the full-total
coprojection of that same bidegree. -/
@[reassoc]
theorem cyclicFirstTwoColumnCell_inclusion (p : Fin 2) (q n : ℕ)
    (h : p.val + q = n) :
    cyclicFirstTwoColumnCell k A p q n h ≫
        (cyclicTwoColumnSequence k A).f.f n =
      (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) p.val q n h :=
  (cyclicBicomplex k A).partialTotalComponent_comp_partialTotalι 1 p q n h

/-- The vanishing of retained cells in the cyclic tail quotient.

The quotient projection from `CC(A)` kills every cell in outer column zero or one. -/
@[reassoc]
theorem cyclicTwoColumnProjection_retained (p : Fin 2) (q n : ℕ)
    (h : p.val + q = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) p.val q n h ≫
        (cyclicTwoColumnSequence k A).g.f n = 0 :=
  (cyclicBicomplex k A).ιTotal_cokernel_partialTotalι_π_eq_zero
    1 p.val q n p.isLt h

/-- The period-two isomorphism of cyclic columns.

Columns `p+2` and `p` have the same parity and differential, so identity maps on their tensor
levels give a chain isomorphism. -/
def cyclicColumnPeriodTwoIso (p : ℕ) : cyclicColumn k A (p + 2) ≅ cyclicColumn k A p :=
  HomologicalComplex.Hom.isoOfComponents (fun q => Iso.refl (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q))
    (fun i j _ => by
      change (𝟙 _) ≫
          (if Even p then (bComplex k A).d i j else (bPrimeComplex k A).d i j) =
        (if Even (p + 2) then (bComplex k A).d i j else (bPrimeComplex k A).d i j) ≫
          (𝟙 _)
      simp only [Category.id_comp, Category.comp_id, cyclicColumn_two_parity])

/-- The forward tensor component of cyclic column periodicity.

The forward period-two column comparison is the identity on each coefficient tensor level. -/
lemma cyclicColumnPeriodTwoIso_hom_f (p q : ℕ) :
    (cyclicColumnPeriodTwoIso k A p).hom.f q = 𝟙 (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q) := rfl

/-- The inverse tensor component of cyclic column periodicity.

The inverse period-two column comparison is the identity on each coefficient tensor level. -/
lemma cyclicColumnPeriodTwoIso_inv_f (p q : ℕ) :
    (cyclicColumnPeriodTwoIso k A p).inv.f q = 𝟙 (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q) := rfl

/-- The cyclic bicomplex after removing two outer columns.

Restricting the outer index to columns `p+2` is isomorphic to the cyclic bicomplex, through
the period-two column isomorphisms and the alternating horizontal maps. -/
def cyclicOuterTailTwoIso :
    (cyclicBicomplex k A).restriction (_root_.partialTotalOuterEmbedding 2) ≅
      cyclicBicomplex k A :=
  HomologicalComplex.Hom.isoOfComponents (fun p => cyclicColumnPeriodTwoIso k A p)
    (fun i j hij => by
      have hi : j + 1 = i := hij
      subst i
      apply HomologicalComplex.hom_ext
      intro q
      let R := cyclicBicomplex k A
      let L := R.restriction (_root_.partialTotalOuterEmbedding 2)
      let X : ModuleCat.{max u v} k := NonUnital.chainLevel k A A q
      let a : X ⟶ X := (cyclicColumnPeriodTwoIso k A (j + 1)).hom.f q
      let c : X ⟶ X := (cyclicColumnPeriodTwoIso k A j).hom.f q
      let d : X ⟶ X := (R.d (j + 1) j).f q
      let d' : X ⟶ X := (L.d (j + 1) j).f q
      have ha : a = 𝟙 X := cyclicColumnPeriodTwoIso_hom_f k A (j + 1) q
      have hc : c = 𝟙 X := cyclicColumnPeriodTwoIso_hom_f k A j q
      have hd : d = if Even j then 𝟙 X - cyclicMap k A q else normMap k A q :=
        cyclicBicomplex_horizontal k A j q
      have hd' : d' = if Even (j + 2) then 𝟙 X - cyclicMap k A q else normMap k A q := by
        change ((cyclicBicomplex k A).d ((j + 2) + 1) (j + 2)).f q = _
        exact cyclicBicomplex_horizontal k A (j + 2) q
      have hdd : d = d' := by
        rw [hd, hd']
        simp only [cyclicColumn_two_parity]
      change a ≫ d = d' ≫ c
      exact (congrArg (fun f : X ⟶ X => f ≫ d) ha).trans
        ((Category.id_comp d).trans (hdd.trans
          ((Category.comp_id d').symm.trans
            (congrArg (fun f : X ⟶ X => d' ≫ f) hc.symm)))))

/-- The forward cell formula for cyclic outer-tail periodicity.

The outer-tail comparison is the identity on every bidegree tensor cell. -/
lemma cyclicOuterTailTwoIso_hom_f_f (p q : ℕ) :
    ((cyclicOuterTailTwoIso k A).hom.f p).f q = 𝟙 (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q) := rfl

/-- The inverse cell formula for cyclic outer-tail periodicity.

The inverse outer-tail comparison is the identity on every bidegree tensor cell. -/
lemma cyclicOuterTailTwoIso_inv_f_f (p q : ℕ) :
    ((cyclicOuterTailTwoIso k A).inv.f p).f q = 𝟙 (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q) := rfl

section Maps

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The cyclic two-column sequence map of a nonunital homomorphism.

A nonunital ground-algebra map `f : A → B` acts on each tensor factor and induces maps on the
retained-column total, full cyclic total, and cokernel tail. -/
def cyclicTwoColumnSequenceMap (f : A →ₙₐ[k] B) :
    cyclicTwoColumnSequence k A ⟶ cyclicTwoColumnSequence k B :=
  partialTotalCokernelShortComplexMap (cyclicBicomplexHom f) 1

/-- The retained-column component of a cyclic sequence map.

The first component of the sequence map induced by `f` is its partial-total map on columns
zero and one. -/
lemma cyclicTwoColumnSequenceMap_τ₁ (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₁ =
      (cyclicBicomplex k A).partialTotalHom (cyclicBicomplexHom f) 1 := rfl

/-- The full-total component of a cyclic sequence map.

The middle component of the sequence map induced by `f` is the total map of the cyclic
bicomplex homomorphism. -/
lemma cyclicTwoColumnSequenceMap_τ₂ (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₂ =
      HomologicalComplex₂.total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ) := rfl

/-- The cokernel component of a cyclic sequence map.

The third component is the cokernel map induced by `f` on the quotient by columns zero and
one. -/
lemma cyclicTwoColumnSequenceMap_τ₃ (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₃ =
      partialTotalCokernelMap (cyclicBicomplexHom f) 1 := rfl

/-- Naturality of retained cyclic cell inclusions.

For `f : A → B`, mapping a retained bidegree cell into `CC^{(2)}(A)` and then applying the
partial-total map equals applying `f` to every tensor entry and including the target cell. -/
@[reassoc]
theorem cyclicFirstTwoColumnCell_naturality (f : A →ₙₐ[k] B)
    (p : Fin 2) (q n : ℕ) (h : p.val + q = n) :
    cyclicFirstTwoColumnCell k A p q n h ≫
        (cyclicTwoColumnSequenceMap f).τ₁.f n =
      ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) q) ≫
        cyclicFirstTwoColumnCell k B p q n h := by
  rw [cyclicTwoColumnSequenceMap_τ₁]
  exact ((cyclicBicomplex k A).partialTotalComponent_naturality
    (cyclicBicomplexHom f) 1 p q n h).trans
      (congrArg (fun m => m ≫ cyclicFirstTwoColumnCell k B p q n h)
        (cyclicBicomplexHom_f_f f p.val q))

/-- Naturality of the two-column cyclic inclusion.

The retained-column map induced by `f` commutes with inclusion into the full cyclic total. -/
@[reassoc]
theorem cyclicTwoColumnInclusion_naturality (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₁ ≫ (cyclicTwoColumnSequence k B).f =
      (cyclicTwoColumnSequence k A).f ≫ (cyclicTwoColumnSequenceMap f).τ₂ :=
  (cyclicTwoColumnSequenceMap f).comm₁₂

/-- Naturality of the two-column cyclic quotient projection.

The full cyclic-total map induced by `f` commutes with projection to the cokernel tail. -/
@[reassoc]
theorem cyclicTwoColumnProjection_naturality (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₂ ≫ (cyclicTwoColumnSequence k B).g =
      (cyclicTwoColumnSequence k A).g ≫ (cyclicTwoColumnSequenceMap f).τ₃ :=
  (cyclicTwoColumnSequenceMap f).comm₂₃

/-- The identity map of the cyclic two-column sequence.

The identity nonunital algebra homomorphism induces the identity on the full inclusion-and-
quotient sequence. -/
lemma cyclicTwoColumnSequenceMap_id :
    cyclicTwoColumnSequenceMap (NonUnitalAlgHom.id k A) =
      𝟙 (cyclicTwoColumnSequence k A) := by
  rw [cyclicTwoColumnSequenceMap, cyclicBicomplexHom_id]
  exact partialTotalCokernelShortComplexMap_id (cyclicBicomplex k A) 1

variable {D : Type v} [NonUnitalRing D] [Module k D]
  [IsScalarTower k D D] [SMulCommClass k D D]

/-- Composition of cyclic two-column sequence maps.

For composable nonunital algebra maps, the sequence map of their composite is the composite of
their sequence maps. -/
lemma cyclicTwoColumnSequenceMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) :
    cyclicTwoColumnSequenceMap (g.comp f) =
      cyclicTwoColumnSequenceMap f ≫ cyclicTwoColumnSequenceMap g := by
  rw [cyclicTwoColumnSequenceMap, cyclicBicomplexHom_comp]
  exact partialTotalCokernelShortComplexMap_comp (cyclicBicomplexHom f)
    (cyclicBicomplexHom g) 1

/-- Naturality of cyclic bicomplex period-two restriction.

The outer-tail comparison commutes with the bicomplex maps induced by nonunital algebra
homomorphisms. -/
@[reassoc]
theorem cyclicOuterTailTwoIso_naturality (f : A →ₙₐ[k] B) :
    HomologicalComplex.restrictionMap (cyclicBicomplexHom f)
        (_root_.partialTotalOuterEmbedding 2) ≫ (cyclicOuterTailTwoIso k B).hom =
      (cyclicOuterTailTwoIso k A).hom ≫ cyclicBicomplexHom f := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  let X : ModuleCat.{max u v} k := NonUnital.chainLevel k A A q
  let Y : ModuleCat.{max u v} k := NonUnital.chainLevel k B B q
  let a : X ⟶ Y := ((cyclicBicomplexHom f).f (p + 2)).f q
  let b : X ⟶ Y := ((cyclicBicomplexHom f).f p).f q
  let eA : X ⟶ X := ((cyclicOuterTailTwoIso k A).hom.f p).f q
  let eB : Y ⟶ Y := ((cyclicOuterTailTwoIso k B).hom.f p).f q
  have ha : a = ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) q) :=
    cyclicBicomplexHom_f_f f (p + 2) q
  have hb : b = ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) q) :=
    cyclicBicomplexHom_f_f f p q
  have heA : eA = 𝟙 X := cyclicOuterTailTwoIso_hom_f_f k A p q
  have heB : eB = 𝟙 Y := cyclicOuterTailTwoIso_hom_f_f k B p q
  change a ≫ eB = eA ≫ b
  exact (congrArg (fun e : Y ⟶ Y => a ≫ e) heB).trans
    ((Category.comp_id a).trans ((ha.trans hb.symm).trans
      ((Category.id_comp b).symm.trans (congrArg (fun e : X ⟶ X => e ≫ b) heA.symm))))

end Maps

end ModuleCat.Algebra.Hochschild

namespace ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The connective period-two description of the cyclic tail.

The quotient of the cyclic total by its first two columns is isomorphic to the cyclic total
extended along `n ↦ n+2`, with zero terms below degree two. -/
def cyclicTwoColumnTailNatIso :
    cyclicTwoColumnTail k A ≅
      (cyclicTotal k A).extend (_root_.partialTotalOuterEmbedding 2) :=
  firstTwoColumnCokernelTailIso (cyclicBicomplex k A) ≪≫
    ((_root_.partialTotalOuterEmbedding 2).extendFunctor
      (ModuleCat.{max u v} k)).mapIso
        ((totalFunctor (ModuleCat.{max u v} k) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).mapIso (cyclicOuterTailTwoIso k A))

/-- Vanishing of cyclic tail terms below degree two.

The two-column cokernel tail has a zero object in each degree `n<2`. -/
theorem isZero_cyclicTwoColumnTail_X (n : ℕ) (hn : n < 2) :
    IsZero ((cyclicTwoColumnTail k A).X n) := by
  let e := _root_.partialTotalOuterEmbedding 2
  have hZero : IsZero (((cyclicTotal k A).extend e).X n) :=
    (cyclicTotal k A).isZero_extend_X e n (by
      intro i hi
      change i + 2 = n at hi
      omega)
  exact hZero.of_iso
    ((HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n).mapIso
      (cyclicTwoColumnTailNatIso k A))

/-- The integer-graded period-two cyclic tail comparison.

After extension from `ℕ` to `ℤ`, the two-column tail is isomorphic to the full cyclic total
extended by the degree-two embedding. -/
def cyclicTwoColumnTailIso :
    (cyclicTwoColumnTail k A).extend (ComplexShape.embeddingDownNatToIntShift 0) ≅
      (cyclicTotal k A).extend (ComplexShape.embeddingDownNatToIntShift 2) :=
  ((ComplexShape.embeddingDownNatToIntShift 0).extendFunctor
      (ModuleCat.{max u v} k)).mapIso (cyclicTwoColumnTailNatIso k A) ≪≫
    HomologicalComplex.extendNatAddIntIso (cyclicTotal k A) 2

/-- The SBI presentation from two cyclic bicomplex columns.

The short exact sequence `0 → CC^{(2)}(A) → CC(A) → Q(A) → 0` and the period-two tail
comparison define a Connes SBI presentation with ordinary complex `CC^{(2)}(A)`. -/
def cyclicConnesSBIPresentation :
    CategoryTheory.ConnesSBIPresentation (A := ModuleCat.{max u v} k) where
  ordinary := cyclicFirstTwoColumns k A
  shortComplex := cyclicTwoColumnSequence k A
  shortExact := cyclicTwoColumnSequence_shortExact k A
  ordinaryComparison := 𝟙 (cyclicFirstTwoColumns k A)
  ordinaryComparisonQuasiIso := inferInstance
  tailIso := cyclicTwoColumnTailIso k A

/-- The homology of the two-column cyclic presentation.

In degree `n`, this is `H_n(CC^{(2)}(A))`, where `CC^{(2)}(A)` is the total of cyclic columns
zero and one. This is the ordinary homology term of the two-column SBI presentation. -/
abbrev cyclicRawHochschildHomology (n : ℕ) : ModuleCat.{max u v} k :=
  (cyclicFirstTwoColumns k A).homology n

/-- The two-column SBI inclusion on homology.

The retained-column inclusion induces `I_n : H_n(CC^{(2)}(A)) → HC_n(A)`. -/
abbrev cyclicSBIInclusion (n : ℕ) :
    cyclicRawHochschildHomology k A n ⟶ cyclicHomology k A n :=
  (cyclicConnesSBIPresentation k A).I n

/-- The two-column cyclic periodicity map.

The cokernel projection and period-two tail comparison induce `S_n : HC_(n+2)(A) → HC_n(A)`. -/
abbrev cyclicSBIPeriodicity (n : ℕ) : cyclicHomology k A (n + 2) ⟶ cyclicHomology k A n :=
  (cyclicConnesSBIPresentation k A).S n

/-- The two-column SBI connecting map.

The connecting morphism of the short exact sequence, with the period-two tail coordinate,
gives `B_n : HC_n(A) → H_(n+1)(CC^{(2)}(A))`. -/
abbrev cyclicSBIConnecting (n : ℕ) :
    cyclicHomology k A n ⟶ cyclicRawHochschildHomology k A (n + 1) :=
  (cyclicConnesSBIPresentation k A).B n

/-- The forward ordinary homology coordinate in two-column SBI.

The ordinary comparison is the identity on `CC^{(2)}(A)`, so its induced forward homology
isomorphism is the identity in every degree. -/
theorem cyclicConnes_hIso_hom (n : ℕ) :
    ((cyclicConnesSBIPresentation k A).hIso n).hom =
      𝟙 (cyclicRawHochschildHomology k A n) := by
  have hDef : ((cyclicConnesSBIPresentation k A).hIso n).hom =
      HomologicalComplex.homologyMap (𝟙 (cyclicFirstTwoColumns k A)) n := rfl
  exact hDef.trans (HomologicalComplex.homologyMap_id (cyclicFirstTwoColumns k A) n)

/-- The inverse ordinary homology coordinate in two-column SBI.

The inverse homology isomorphism of the identity ordinary comparison is the identity on
`H_n(CC^{(2)}(A))`. -/
theorem cyclicConnes_hIso_inv (n : ℕ) :
    ((cyclicConnesSBIPresentation k A).hIso n).inv =
      𝟙 (cyclicRawHochschildHomology k A n) := by
  let X : ModuleCat.{max u v} k := cyclicRawHochschildHomology k A n
  let E : X ≅ X := (cyclicConnesSBIPresentation k A).hIso n
  have hE : E.hom = 𝟙 X := cyclicConnes_hIso_hom k A n
  apply (cancel_mono E.hom).1
  exact E.inv_hom_id.trans ((Category.id_comp E.hom).trans hE).symm

/-- The two-column inclusion as a chain-induced homology map.

The SBI map `I_n` equals the homology map of the inclusion `CC^{(2)}(A) → CC(A)`. -/
theorem cyclicSBIInclusion_eq_homologyMap (n : ℕ) :
    cyclicSBIInclusion k A n =
      HomologicalComplex.homologyMap (cyclicTwoColumnSequence k A).f n := by
  let X : ModuleCat.{max u v} k := cyclicRawHochschildHomology k A n
  let E : X ≅ X := (cyclicConnesSBIPresentation k A).hIso n
  let f : X ⟶ cyclicHomology k A n := HomologicalComplex.homologyMap (cyclicTwoColumnSequence k A).f n
  have hE : E.hom = 𝟙 X := cyclicConnes_hIso_hom k A n
  change E.hom ≫ f = f
  exact (congrArg (fun e : X ⟶ X => e ≫ f) hE).trans (Category.id_comp f)

/-- The translated long-exact boundary in two-column SBI.

The map `B_n` is the inverse tail-homology coordinate followed by the short-exact-sequence
boundary from degree `n+2` of the tail to degree `n+1` of the retained-column total. -/
theorem cyclicSBIConnecting_eq_δ (n : ℕ) :
    cyclicSBIConnecting k A n =
      ((cyclicConnesSBIPresentation k A).tailHomologyIso n).inv ≫
        (cyclicTwoColumnSequence_shortExact k A).δ (n + 2) (n + 1) (by simp) := by
  let X : ModuleCat.{max u v} k := cyclicRawHochschildHomology k A (n + 1)
  let E : X ≅ X := (cyclicConnesSBIPresentation k A).hIso (n + 1)
  let f : cyclicHomology k A n ⟶ X :=
    ((cyclicConnesSBIPresentation k A).tailHomologyIso n).inv ≫
      (cyclicTwoColumnSequence_shortExact k A).δ (n + 2) (n + 1) (by simp)
  have hE : E.inv = 𝟙 X := cyclicConnes_hIso_inv k A (n + 1)
  change f ≫ E.inv = f
  exact (congrArg (fun e : X ⟶ X => f ≫ e) hE).trans (Category.comp_id f)

/-- The connective homology diagram of two-column SBI.

The maps `I`, `S`, and `B` of the two-column presentation give the SBI diagram in all
nonnegative degrees. -/
abbrev cyclicSBIDiagram : CategoryTheory.NatSBIDiagram (A := ModuleCat.{max u v} k) :=
  (cyclicConnesSBIPresentation k A).sbiDiagram

/-- Exactness of the two-column SBI diagram.

The two-column homology and cyclic homology maps are exact at every term of the connective SBI
diagram, by the long exact sequence of the cyclic short complex. -/
theorem cyclicSBIDiagram_exact : (cyclicSBIDiagram k A).Exact :=
  (cyclicConnesSBIPresentation k A).sbiDiagram_exact

/-- The low-degree conditions of two-column SBI.

The vanishing of the cokernel tail below degree two gives the connective boundary conditions
of the SBI diagram. -/
theorem cyclicSBIDiagram_connectiveBoundary : (cyclicSBIDiagram k A).ConnectiveBoundary :=
  (cyclicConnesSBIPresentation k A).sbiDiagram_connectiveBoundary

/-- The degree-zero isomorphism of two-column SBI.

The inclusion `H_0(CC^{(2)}(A)) → HC_0(A)` is an isomorphism. -/
theorem cyclicSBIInclusion_isIso_zero : IsIso (cyclicSBIInclusion k A 0) :=
  (cyclicConnesSBIPresentation k A).isIso_I_zero

/-- The degree-one epimorphism of two-column SBI.

The inclusion `H_1(CC^{(2)}(A)) → HC_1(A)` is epic. -/
theorem cyclicSBIInclusion_epi_one : Epi (cyclicSBIInclusion k A 1) :=
  (cyclicConnesSBIPresentation k A).epi_I_one

section PresentationMaps

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Naturality of the connective cyclic-tail comparison.

The cokernel-tail map induced by `f : A → B` commutes with the degree-two extension of the
full cyclic-total map. -/
@[reassoc]
theorem cyclicTwoColumnTailNatIso_hom_naturality (f : A →ₙₐ[k] B) :
    partialTotalCokernelMap (cyclicBicomplexHom f) 1 ≫ (cyclicTwoColumnTailNatIso k B).hom =
      (cyclicTwoColumnTailNatIso k A).hom ≫
        HomologicalComplex.extendMap
          (total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ))
          (_root_.partialTotalOuterEmbedding 2) := by
  let C := ModuleCat.{max u v} k
  let R : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
  let T : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k B
  let F : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤ ChainComplex C ℕ :=
    totalFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := _root_.partialTotalOuterEmbedding 2
  let ψ : R ⟶ T := cyclicBicomplexHom f
  let ψTail : R.restriction e ⟶ T.restriction e := HomologicalComplex.restrictionMap ψ e
  let aA : cyclicTwoColumnTail k A ≅ (F.obj (R.restriction e)).extend e := firstTwoColumnCokernelTailIso R
  let aB : cyclicTwoColumnTail k B ≅ (F.obj (T.restriction e)).extend e := firstTwoColumnCokernelTailIso T
  let pA : F.obj (R.restriction e) ≅ cyclicTotal k A := F.mapIso (cyclicOuterTailTwoIso k A)
  let pB : F.obj (T.restriction e) ≅ cyclicTotal k B := F.mapIso (cyclicOuterTailTwoIso k B)
  let bA : (F.obj (R.restriction e)).extend e ≅ (cyclicTotal k A).extend e := (e.extendFunctor C).mapIso pA
  let bB : (F.obj (T.restriction e)).extend e ≅ (cyclicTotal k B).extend e := (e.extendFunctor C).mapIso pB
  have ha : partialTotalCokernelMap ψ 1 ≫ aB.hom =
      aA.hom ≫ HomologicalComplex.extendMap (F.map ψTail) e :=
    firstTwoColumnCokernelTailIso_hom_naturality ψ
  have hp : F.map ψTail ≫ pB.hom = pA.hom ≫ F.map ψ := by
    change F.map ψTail ≫ F.map (cyclicOuterTailTwoIso k B).hom =
      F.map (cyclicOuterTailTwoIso k A).hom ≫ F.map ψ
    erw [← F.map_comp, cyclicOuterTailTwoIso_naturality, F.map_comp]
  have hb : HomologicalComplex.extendMap (F.map ψTail) e ≫ bB.hom =
      bA.hom ≫ HomologicalComplex.extendMap (F.map ψ) e := by
    change HomologicalComplex.extendMap (F.map ψTail) e ≫
        HomologicalComplex.extendMap pB.hom e =
      HomologicalComplex.extendMap pA.hom e ≫ HomologicalComplex.extendMap (F.map ψ) e
    erw [← HomologicalComplex.extendMap_comp, hp, HomologicalComplex.extendMap_comp]
    rfl
  change partialTotalCokernelMap ψ 1 ≫ (aB.hom ≫ bB.hom) =
    (aA.hom ≫ bA.hom) ≫ HomologicalComplex.extendMap (F.map ψ) e
  have hFirst : partialTotalCokernelMap ψ 1 ≫ (aB.hom ≫ bB.hom) =
      (aA.hom ≫ HomologicalComplex.extendMap (F.map ψTail) e) ≫ bB.hom :=
    (Category.assoc (partialTotalCokernelMap ψ 1) aB.hom bB.hom).symm.trans
      (congrArg (fun g : cyclicTwoColumnTail k A ⟶ (F.obj (T.restriction e)).extend e =>
        g ≫ bB.hom) ha)
  have hSecond : (aA.hom ≫ HomologicalComplex.extendMap (F.map ψTail) e) ≫ bB.hom =
      aA.hom ≫ (bA.hom ≫ HomologicalComplex.extendMap (F.map ψ) e) :=
    (Category.assoc aA.hom (HomologicalComplex.extendMap (F.map ψTail) e) bB.hom).trans
      (congrArg (fun g : (F.obj (R.restriction e)).extend e ⟶ (cyclicTotal k B).extend e =>
        aA.hom ≫ g) hb)
  exact hFirst.trans (hSecond.trans
    (Category.assoc aA.hom bA.hom (HomologicalComplex.extendMap (F.map ψ) e)).symm)

/-- Naturality of the integer-graded cyclic-tail comparison.

The integer extensions of the cokernel-tail map and full cyclic-total map commute with the
period-two tail isomorphism. -/
@[reassoc]
theorem cyclicTwoColumnTailIso_hom_naturality (f : A →ₙₐ[k] B) :
    HomologicalComplex.extendMap (partialTotalCokernelMap (cyclicBicomplexHom f) 1)
        (ComplexShape.embeddingDownNatToIntShift 0) ≫ (cyclicTwoColumnTailIso k B).hom =
      (cyclicTwoColumnTailIso k A).hom ≫
        HomologicalComplex.extendMap
          (total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ))
          (ComplexShape.embeddingDownNatToIntShift 2) := by
  let C := ModuleCat.{max u v} k
  let e₀ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) := ComplexShape.embeddingDownNatToIntShift 0
  let e₂ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) := ComplexShape.embeddingDownNatToIntShift 2
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := _root_.partialTotalOuterEmbedding 2
  let ψ : cyclicTotal k A ⟶ cyclicTotal k B := total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ)
  let q : cyclicTwoColumnTail k A ⟶ cyclicTwoColumnTail k B := partialTotalCokernelMap (cyclicBicomplexHom f) 1
  let aA : (cyclicTwoColumnTail k A).extend e₀ ≅ ((cyclicTotal k A).extend e).extend e₀ :=
    (e₀.extendFunctor C).mapIso (cyclicTwoColumnTailNatIso k A)
  let aB : (cyclicTwoColumnTail k B).extend e₀ ≅ ((cyclicTotal k B).extend e).extend e₀ :=
    (e₀.extendFunctor C).mapIso (cyclicTwoColumnTailNatIso k B)
  let bA : ((cyclicTotal k A).extend e).extend e₀ ≅ (cyclicTotal k A).extend e₂ :=
    HomologicalComplex.extendNatAddIntIso (cyclicTotal k A) 2
  let bB : ((cyclicTotal k B).extend e).extend e₀ ≅ (cyclicTotal k B).extend e₂ :=
    HomologicalComplex.extendNatAddIntIso (cyclicTotal k B) 2
  have ha : HomologicalComplex.extendMap q e₀ ≫ aB.hom =
      aA.hom ≫ HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀ := by
    change HomologicalComplex.extendMap q e₀ ≫
        HomologicalComplex.extendMap (cyclicTwoColumnTailNatIso k B).hom e₀ =
      HomologicalComplex.extendMap (cyclicTwoColumnTailNatIso k A).hom e₀ ≫
        HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀
    erw [← HomologicalComplex.extendMap_comp, cyclicTwoColumnTailNatIso_hom_naturality,
      HomologicalComplex.extendMap_comp]
  have hb : HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀ ≫
      bB.hom = bA.hom ≫ HomologicalComplex.extendMap ψ e₂ :=
    HomologicalComplex.extendNatAddIntIso_hom_naturality ψ 2
  change HomologicalComplex.extendMap q e₀ ≫ (aB.hom ≫ bB.hom) =
    (aA.hom ≫ bA.hom) ≫ HomologicalComplex.extendMap ψ e₂
  calc
    HomologicalComplex.extendMap q e₀ ≫ (aB.hom ≫ bB.hom) =
        (HomologicalComplex.extendMap q e₀ ≫ aB.hom) ≫ bB.hom := (Category.assoc _ _ _).symm
    _ = (aA.hom ≫ HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀) ≫
          bB.hom := by rw [ha]
    _ = aA.hom ≫ (HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀ ≫
          bB.hom) := Category.assoc _ _ _
    _ = aA.hom ≫ (bA.hom ≫ HomologicalComplex.extendMap ψ e₂) := by rw [hb]
    _ = (aA.hom ≫ bA.hom) ≫ HomologicalComplex.extendMap ψ e₂ :=
      (Category.assoc _ _ _).symm

/-- The two-column SBI presentation map of a nonunital homomorphism.

A nonunital ground-algebra map induces a morphism of the two-column SBI presentations, using
its retained-column map, cyclic sequence map, and natural tail comparison. -/
def cyclicConnesSBIPresentationMap (f : A →ₙₐ[k] B) :
    cyclicConnesSBIPresentation k A ⟶ cyclicConnesSBIPresentation k B where
  ordinaryMap := (cyclicTwoColumnSequenceMap f).τ₁
  shortMap := cyclicTwoColumnSequenceMap f
  ordinaryComparison_naturality := by
    change (cyclicTwoColumnSequenceMap f).τ₁ ≫ 𝟙 _ = 𝟙 _ ≫ (cyclicTwoColumnSequenceMap f).τ₁
    rw [Category.comp_id, Category.id_comp]
  tailIso_naturality := by
    change HomologicalComplex.extendMap (partialTotalCokernelMap (cyclicBicomplexHom f) 1)
        (ComplexShape.embeddingDownNatToIntShift 0) ≫ (cyclicTwoColumnTailIso k B).hom =
      (cyclicTwoColumnTailIso k A).hom ≫ HomologicalComplex.extendMap
        (total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ))
        (ComplexShape.embeddingDownNatToIntShift 2)
    exact cyclicTwoColumnTailIso_hom_naturality f

/-- The short-complex component of a two-column presentation map.

The short-complex component is the inclusion-and-cokernel sequence map induced by the
nonunital algebra homomorphism. -/
lemma cyclicConnesSBIPresentationMap_shortMap (f : A →ₙₐ[k] B) :
    (cyclicConnesSBIPresentationMap f).shortMap = cyclicTwoColumnSequenceMap f := rfl

/-- The ordinary component of a two-column presentation map.

The ordinary chain map acts on the total of the retained two columns. -/
lemma cyclicConnesSBIPresentationMap_ordinaryMap (f : A →ₙₐ[k] B) :
    (cyclicConnesSBIPresentationMap f).ordinaryMap = (cyclicTwoColumnSequenceMap f).τ₁ := rfl

/-- The identity morphism of a two-column SBI presentation.

The identity nonunital algebra homomorphism induces the identity presentation morphism. -/
lemma cyclicConnesSBIPresentationMap_id :
    cyclicConnesSBIPresentationMap (NonUnitalAlgHom.id k A) =
      𝟙 (cyclicConnesSBIPresentation k A) := by
  apply CategoryTheory.ConnesSBIPresentation.hom_ext
  · change (cyclicTwoColumnSequenceMap (NonUnitalAlgHom.id k A)).τ₁ = 𝟙 _
    rw [cyclicTwoColumnSequenceMap_id, ShortComplex.id_τ₁]
  · exact cyclicTwoColumnSequenceMap_id (k := k) (A := A)

variable {D : Type v} [NonUnitalRing D] [Module k D]
  [IsScalarTower k D D] [SMulCommClass k D D]

/-- Composition of two-column SBI presentation morphisms.

The presentation morphism induced by a composite nonunital algebra map is the composite of the
induced presentation morphisms. -/
lemma cyclicConnesSBIPresentationMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) :
    cyclicConnesSBIPresentationMap (g.comp f) =
      cyclicConnesSBIPresentationMap f ≫ cyclicConnesSBIPresentationMap g := by
  apply CategoryTheory.ConnesSBIPresentation.hom_ext
  · change (cyclicTwoColumnSequenceMap (g.comp f)).τ₁ =
      (cyclicTwoColumnSequenceMap f).τ₁ ≫ (cyclicTwoColumnSequenceMap g).τ₁
    rw [cyclicTwoColumnSequenceMap_comp, ShortComplex.comp_τ₁]
  · exact cyclicTwoColumnSequenceMap_comp f g

/-- The two-column SBI homology map of an algebra homomorphism.

A nonunital ground-algebra map induces a morphism of connective SBI diagrams through its two-
column presentation map. -/
def cyclicSBIDiagramMap (f : A →ₙₐ[k] B) : cyclicSBIDiagram k A ⟶ cyclicSBIDiagram k B :=
  (cyclicConnesSBIPresentationMap f).toSBIHom

/-- The ordinary homology component of a two-column SBI map.

In degree `n`, the ordinary component is the homology map of the retained-column chain map. -/
lemma cyclicSBIDiagramMap_hMap (f : A →ₙₐ[k] B) (n : ℕ) :
    (cyclicSBIDiagramMap f).hMap n =
      HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n := rfl

/-- The cyclic homology component of a two-column SBI map.

In degree `n`, the cyclic component is the cyclic-homology map induced by the algebra
homomorphism. -/
lemma cyclicSBIDiagramMap_hcMap (f : A →ₙₐ[k] B) (n : ℕ) :
    (cyclicSBIDiagramMap f).hcMap n = cyclicHomologyMap f n := rfl

/-- The identity map of a two-column SBI homology diagram.

The identity algebra homomorphism induces the identity on the ordinary and cyclic homology
terms and their SBI diagram. -/
lemma cyclicSBIDiagramMap_id :
    cyclicSBIDiagramMap (NonUnitalAlgHom.id k A) = 𝟙 (cyclicSBIDiagram k A) := by
  rw [cyclicSBIDiagramMap, cyclicConnesSBIPresentationMap_id]
  exact CategoryTheory.ConnesSBIPresentation.Hom.toSBIHom_id (cyclicConnesSBIPresentation k A)

/-- Composition of two-column SBI homology diagram maps.

The SBI diagram map of a composite algebra homomorphism equals the composite of the two
diagram maps. -/
lemma cyclicSBIDiagramMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) :
    cyclicSBIDiagramMap (g.comp f) = cyclicSBIDiagramMap f ≫ cyclicSBIDiagramMap g := by
  rw [cyclicSBIDiagramMap, cyclicConnesSBIPresentationMap_comp]
  exact CategoryTheory.ConnesSBIPresentation.Hom.toSBIHom_comp
    (cyclicConnesSBIPresentationMap f) (cyclicConnesSBIPresentationMap g)

/-- Naturality of the two-column SBI homology inclusion.

For a nonunital algebra map, the ordinary and cyclic homology maps commute with `I_n :
H_n(CC^{(2)}) → HC_n`. -/
@[reassoc]
theorem cyclicSBIInclusion_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (cyclicSBIDiagramMap f).hMap n ≫ cyclicSBIInclusion k B n =
      cyclicSBIInclusion k A n ≫ cyclicHomologyMap f n :=
  (cyclicSBIDiagramMap f).I_naturality n |>.symm

/-- Naturality of two-column cyclic periodicity.

For a nonunital algebra map, its cyclic-homology maps in degrees `n+2` and `n` commute with
`S_n`. -/
@[reassoc]
theorem cyclicSBIPeriodicity_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMap f (n + 2) ≫ cyclicSBIPeriodicity k B n =
      cyclicSBIPeriodicity k A n ≫ cyclicHomologyMap f n :=
  (cyclicSBIDiagramMap f).S_naturality n |>.symm

/-- Naturality of the two-column SBI boundary.

For a nonunital algebra map, its cyclic homology map in degree `n` and two-column homology map
in degree `n+1` commute with `B_n`. -/
@[reassoc]
theorem cyclicSBIConnecting_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMap f n ≫ cyclicSBIConnecting k B n =
      cyclicSBIConnecting k A n ≫ (cyclicSBIDiagramMap f).hMap (n + 1) :=
  (cyclicSBIDiagramMap f).B_naturality n |>.symm

/-- A cyclic-total quasi-isomorphism from a two-column comparison.

If a nonunital algebra map induces a quasi-isomorphism on the first-two-column totals, it
induces a quasi-isomorphism on the full cyclic totals. -/
theorem cyclicTotalHom_quasiIso_of_firstTwo (f : A →ₙₐ[k] B)
    [QuasiIso (cyclicTwoColumnSequenceMap f).τ₁] : QuasiIso (cyclicTotalHom f) := by
  let F := cyclicConnesSBIPresentationMap f
  letI : QuasiIso F.ordinaryMap := by
    change QuasiIso (cyclicTwoColumnSequenceMap f).τ₁
    infer_instance
  change QuasiIso F.shortMap.τ₂
  exact F.quasiIso_shortMap_τ₂

end PresentationMaps

end ModuleCat.Algebra.Hochschild


namespace ModuleCat.Algebra.Hochschild

section ReverseComparison

variable {k : Type u} [CommRing k] {A B : Type v}
  [NonUnitalRing A] [NonUnitalRing B] [Module k A] [Module k B]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- A two-column quasi-isomorphism from a cyclic-total comparison.

If a nonunital algebra map induces a quasi-isomorphism on the full cyclic totals, it induces a
quasi-isomorphism on the first-two-column totals. -/
theorem cyclicFirstTwoMap_quasiIso_of_cyclicTotalHom (f : A →ₙₐ[k] B)
    [QuasiIso (cyclicTotalHom f)] : QuasiIso (cyclicTwoColumnSequenceMap f).τ₁ := by
  let F := cyclicConnesSBIPresentationMap f
  letI : QuasiIso F.shortMap.τ₂ := by
    change QuasiIso (cyclicTotalHom f)
    infer_instance
  change QuasiIso F.ordinaryMap
  exact F.quasiIso_ordinaryMap

/-- The equivalence of two-column and cyclic-total quasi-isomorphisms.

For a nonunital ground-algebra homomorphism, its map on the retained two-column total is a
quasi-isomorphism if and only if its full cyclic-total map is a quasi-isomorphism. -/
theorem cyclicFirstTwoMap_quasiIso_iff_cyclicTotalHom (f : A →ₙₐ[k] B) :
    QuasiIso (cyclicTwoColumnSequenceMap f).τ₁ ↔ QuasiIso (cyclicTotalHom f) := by
  change QuasiIso (cyclicConnesSBIPresentationMap f).ordinaryMap ↔
    QuasiIso (cyclicConnesSBIPresentationMap f).shortMap.τ₂
  exact (cyclicConnesSBIPresentationMap f).quasiIso_ordinaryMap_iff_shortMap_τ₂

/-- The equivalence of two-column and cyclic homology isomorphisms.

For a nonunital ground-algebra map, the induced maps on `H_n(CC^{(2)})` are isomorphisms for
all `n` if and only if the maps on `HC_n` are isomorphisms for all `n`. -/
theorem cyclicRawHochschildMap_isIso_iff_cyclicHomologyMap (f : A →ₙₐ[k] B) :
    (∀ n : ℕ, IsIso (HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n)) ↔
      ∀ n : ℕ, IsIso (cyclicHomologyMap f n) := by
  let h : cyclicFirstTwoColumns k A ⟶ cyclicFirstTwoColumns k B := (cyclicTwoColumnSequenceMap f).τ₁
  let c : cyclicTotal k A ⟶ cyclicTotal k B := cyclicTotalHom f
  have hh : QuasiIso h ↔ ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap h n) :=
    (_root_.quasiIso_iff h).trans
      (forall_congr' (fun n => _root_.quasiIsoAt_iff_isIso_homologyMap h n))
  have hc : QuasiIso c ↔ ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap c n) :=
    (_root_.quasiIso_iff c).trans
      (forall_congr' (fun n => _root_.quasiIsoAt_iff_isIso_homologyMap c n))
  change (∀ n : ℕ, IsIso (HomologicalComplex.homologyMap h n)) ↔
    ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap c n)
  exact hh.symm.trans ((cyclicFirstTwoMap_quasiIso_iff_cyclicTotalHom f).trans hc)

end ReverseComparison

end ModuleCat.Algebra.Hochschild
