/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.TensorNormalization
public import Mathlib.RingTheory.Congruence.Hom

/-!
# The ordered-word PBW basis and its coefficient maps

Let R be a commutative ring and L an R-Lie algebra with an R-module
basis b indexed by a linearly ordered type I. An ordered word is a
finite weakly increasing list in I, and its value in U = U_R(L) is
the ordered product ι(b_(i₁)) ⋯ ι(b_(iₙ)).

The tensor normalizer takes values in the finitely supported module
N = OrderedWord(I) →₀ R. Contextual equality of normal forms defines
a ring congruence on T_R(L): a ∼ c if
Norm(p a s) = Norm(p c s) for every p,s ∈ T_R(L).
The defining Lie relation belongs to this congruence. Its quotient
therefore receives a Lie map from L, and the enveloping universal
property gives the R-linear PBW coordinates U → N.

Coordinates of an ordered word are its single coordinate vector.
Together with spanning, this gives N ≃ₗ[R] U and the ordered-word
R-basis of U. In particular U is free whenever the underlying
R-module L is free. Extracting the length-one ordered coordinates
gives a map U →ₗ[R] L left inverse to ι, so ι is injective under the
basis hypothesis. The worlds of R, L and I are independent, and I
need not be finite.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

attribute [local implicit_reducible] RingCon.Quotient

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "T" => TensorAlgebra R L
local notation "U" => UniversalEnvelopingAlgebra R L
local notation "N" => (OrderedWord I →₀ R)
local notation "τ" => TensorAlgebra.ι R

attribute [local instance] LieRing.ofAssociativeRing

/-- For a commutative ring R, an R-Lie algebra L and an R-basis
b indexed by linearly ordered I, let Norm : T_R(L) → (OrderedWord(I) →₀ R)
be the tensor normalizer. The congruence relates a,c ∈ T_R(L) when
Norm(p a s) = Norm(p c s) for every prefix and suffix p,s ∈ T_R(L).
This contextual relation is compatible with addition and multiplication. -/
@[implicit_reducible]
def normalizationRingCon (b : Module.Basis I R L) : RingCon T where
  r a c := ∀ p s : T, tensorNormalizer b (p * a * s) = tensorNormalizer b (p * c * s)
  iseqv :=
    { refl := by intro a p s; rfl
      symm := by intro a c h p s; exact (h p s).symm
      trans := by intro a c d h k p s; exact (h p s).trans (k p s) }
  add' := by
    intro a c d e hac hde p s
    simp only [mul_add, add_mul, map_add]
    rw [hac p s, hde p s]
  mul' := by
    intro a c d e hac hde p s
    calc
      tensorNormalizer b (p * (a * d) * s) =
          tensorNormalizer b (p * a * (d * s)) := by simp only [mul_assoc]
      _ = tensorNormalizer b (p * c * (d * s)) := hac p (d * s)
      _ = tensorNormalizer b ((p * c) * d * s) := by simp only [mul_assoc]
      _ = tensorNormalizer b ((p * c) * e * s) := hde (p * c) s
      _ = tensorNormalizer b (p * (c * e) * s) := by simp only [mul_assoc]

/-- For a commutative ring R, an R-Lie algebra L, an ordered
R-basis b and x,y ∈ L, the tensor elements
τ([x,y])+τ(y)τ(x) and τ(x)τ(y) are contextually congruent.
Thus their normal forms agree after multiplication by every tensor
prefix and suffix, where τ : L → T_R(L) is the tensor generator map. -/
theorem normalizationRingCon_lie_compat (b : Module.Basis I R L) (x y : L) :
    normalizationRingCon b (τ ⁅x, y⁆ + τ y * τ x) (τ x * τ y) := by
  intro p s
  have hzero := tensorNormalizer_relationError b p s x y
  simp only [relationError, mul_sub, sub_mul, map_sub] at hzero
  simp only [mul_add, add_mul, map_add]
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hzero)).symm

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b, the normalization quotient is T_R(L) modulo
the ring congruence a ∼ c defined by
Norm(p a s) = Norm(p c s) for every tensor prefix p and suffix s.
It is an R-algebra quotient of the tensor algebra. -/
abbrev NormalizationQuotient (b : Module.Basis I R L) :=
  (normalizationRingCon b).Quotient

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b, the quotient projection
q : T_R(L) →ₐ[R] Q sends a tensor element to its class under
contextual normal-form equality. Here Q is the normalization
ring quotient determined by b. -/
@[implicit_reducible]
def normalizationQuotientMap (b : Module.Basis I R L) : T →ₐ[R] NormalizationQuotient b :=
  RingCon.mkₐ R (normalizationRingCon b)

theorem normalizationQuotientMap_surjective (b : Module.Basis I R L) :
    Function.Surjective (normalizationQuotientMap b) :=
  RingCon.mkₐ_surjective (normalizationRingCon b)

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b indexed by I, the R-linear map
Q → (OrderedWord(I) →₀ R) sends [a] to Norm(a).
It is well-defined because contextual equality includes the
prefix and suffix both equal to 1. -/
def normalizationQuotientCoordinates (b : Module.Basis I R L) :
    NormalizationQuotient b →ₗ[R] N where
  toFun := Quotient.lift (tensorNormalizer b) (by
    intro a c h
    simpa only [one_mul, mul_one] using h (1 : T) (1 : T))
  map_add' x y := by
    obtain ⟨a, rfl⟩ := normalizationQuotientMap_surjective b x
    obtain ⟨c, rfl⟩ := normalizationQuotientMap_surjective b y
    have hadd : normalizationQuotientMap b (a + c) =
        normalizationQuotientMap b a + normalizationQuotientMap b c :=
      (normalizationQuotientMap b).toLinearMap.map_add a c
    rw [← hadd]
    change tensorNormalizer b (a + c) = tensorNormalizer b a + tensorNormalizer b c
    exact (tensorNormalizer b).map_add a c
  map_smul' r x := by
    obtain ⟨a, rfl⟩ := normalizationQuotientMap_surjective b x
    have hsmul : normalizationQuotientMap b (r • a) = r • normalizationQuotientMap b a :=
      (normalizationQuotientMap b).toLinearMap.map_smul r a
    rw [← hsmul]
    change tensorNormalizer b (r • a) = (RingHom.id R) r • tensorNormalizer b a
    simpa only [RingHom.id_apply] using (tensorNormalizer b).map_smul r a

@[simp]
theorem normalizationQuotientCoordinates_mk (b : Module.Basis I R L) (a : T) :
    normalizationQuotientCoordinates b (normalizationQuotientMap b a) =
      tensorNormalizer b a := rfl

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b, the map L →ₗ⁅R⁆ Q sends x to q(τ(x)).
It preserves the Lie bracket because the tensor Lie relation
τ([x,y])+τ(y)τ(x) ∼ τ(x)τ(y) holds in Q.
The bracket on Q is its associative-ring commutator. -/
def normalizationQuotientι (b : Module.Basis I R L) : L →ₗ⁅R⁆ NormalizationQuotient b where
  toLinearMap := (normalizationQuotientMap b).toLinearMap.comp τ
  map_lie' := by
    intro x y
    change normalizationQuotientMap b (τ ⁅x, y⁆) =
      normalizationQuotientMap b (τ x) * normalizationQuotientMap b (τ y) -
        normalizationQuotientMap b (τ y) * normalizationQuotientMap b (τ x)
    have h : normalizationQuotientMap b (τ ⁅x, y⁆ + τ y * τ x) =
        normalizationQuotientMap b (τ x * τ y) :=
      Quotient.sound (normalizationRingCon_lie_compat b x y)
    simp only [map_add, map_mul] at h
    exact eq_sub_iff_add_eq.mpr h

@[simp]
theorem normalizationQuotientι_apply (b : Module.Basis I R L) (x : L) :
    normalizationQuotientι b x = normalizationQuotientMap b (τ x) := rfl

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b indexed by I, the R-linear PBW coordinate map
U_R(L) → (OrderedWord(I) →₀ R) is the normal-form coordinate map
of Q composed with the enveloping lift of x ↦ q(τ(x)).
Its values are finite coefficient families of weakly increasing words. -/
def pbwCoordinates (b : Module.Basis I R L) : U →ₗ[R] N :=
  (normalizationQuotientCoordinates b).comp
    (UniversalEnvelopingAlgebra.lift R (normalizationQuotientι b)).toLinearMap

theorem lift_normalizationQuotientι_basisWord (b : Module.Basis I R L) (xs : List I) :
    UniversalEnvelopingAlgebra.lift R (normalizationQuotientι b) (basisWord b xs) =
      normalizationQuotientMap b (tensorWord b xs) := by
  induction xs with
  | nil => simp only [basisWord_nil, tensorWord_nil, map_one]
  | cons i xs ih =>
      simp only [basisWord_cons, tensorWord_cons, map_mul,
        UniversalEnvelopingAlgebra.lift_ι_apply, normalizationQuotientι_apply, ih]

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b, the PBW coordinates of
ι(b_(i₁)) ⋯ ι(b_(iₙ)) equal the normal form of the list
[i₁,…,iₙ]. The list may be unordered or contain repeated indices. -/
@[simp]
theorem pbwCoordinates_basisWord (b : Module.Basis I R L) (xs : List I) :
    pbwCoordinates b (basisWord b xs) = normalize b xs := by
  change normalizationQuotientCoordinates b
    (UniversalEnvelopingAlgebra.lift R (normalizationQuotientι b) (basisWord b xs)) = _
  rw [lift_normalizationQuotientι_basisWord, normalizationQuotientCoordinates_mk,
    tensorNormalizer_tensorWord]

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b, evaluation of a finite coefficient family of
weakly increasing words followed by PBW coordinates is the identity
on OrderedWord(I) →₀ R. Thus coordinates are a left inverse to
the R-linear ordered-word evaluation map. -/
theorem pbwCoordinates_comp_orderedWordLinear (b : Module.Basis I R L) :
    (pbwCoordinates b).comp (orderedWordLinear b) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro xs r
  rw [LinearMap.comp_apply, orderedWordLinear_single, map_smul,
    orderedWordValue, pbwCoordinates_basisWord, normalize_ordered]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one, LinearMap.id_apply]

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b indexed by I, evaluation is the R-linear equivalence
(OrderedWord(I) →₀ R) ≃ₗ[R] U_R(L).
It sends δ_[i₁,…,iₙ] to ι(b_(i₁)) ⋯ ι(b_(iₙ)), with
i₁ ≤ ⋯ ≤ iₙ; its inverse is the PBW coordinate map. -/
def orderedWordEquiv (b : Module.Basis I R L) : N ≃ₗ[R] U :=
  LinearEquiv.ofBijective (orderedWordLinear b) ⟨
    (show Function.LeftInverse (pbwCoordinates b) (orderedWordLinear b) from
      fun x => LinearMap.congr_fun (pbwCoordinates_comp_orderedWordLinear b) x).injective,
    (LinearMap.range_eq_top.mp (by
      rw [orderedWordLinear, Finsupp.range_linearCombination, orderedWord_spanning]))⟩

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b indexed by I, the R-basis of U_R(L) is indexed
by finite weakly increasing words. Its vector at [i₁,…,iₙ] is
ι(b_(i₁)) ⋯ ι(b_(iₙ)), and the empty-word vector is 1. -/
def orderedBasis (b : Module.Basis I R L) : Module.Basis (OrderedWord I) R U :=
  (Finsupp.basisSingleOne (R := R)).map (orderedWordEquiv b)

@[simp]
theorem orderedBasis_apply (b : Module.Basis I R L) (xs : OrderedWord I) :
    orderedBasis b xs = orderedWordValue b xs := by
  change orderedWordLinear b (Finsupp.single xs 1) = orderedWordValue b xs
  rw [orderedWordLinear_single, one_smul]

theorem orderedWord_linearIndependent (b : Module.Basis I R L) :
    LinearIndependent R (orderedWordValue b) := by
  have h : (orderedBasis b : OrderedWord I → U) = orderedWordValue b :=
    funext (orderedBasis_apply b)
  rw [← h]
  exact (orderedBasis b).linearIndependent

/-- For a commutative ring R and an R-Lie algebra L with an
R-basis b indexed by a linearly ordered type I, the underlying
R-module of U_R(L) is free, with its ordered-word PBW basis.
The index type I may be infinite. -/
theorem free_of_basis (b : Module.Basis I R L) : Module.Free R U :=
  Module.Free.of_basis (orderedBasis b)

/-- For a commutative ring R and an R-Lie algebra L whose
underlying R-module is free, the underlying R-module of U_R(L)
is also free. No finite-rank hypothesis is imposed on L. -/
theorem free_of_free [Module.Free R L] : Module.Free R U := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) := linearOrderOfSTO WellOrderingRel
  exact free_of_basis (Module.Free.chooseBasis R L)

/-- For a commutative ring R and an R-Lie algebra L with
ordered basis b, the degree-one projection U_R(L) →ₗ[R] L sends
an element with PBW coefficients c to ∑_i c_[i] • b_i.
Only singleton ordered words contribute; the empty word and ordered
words of other lengths contribute zero. -/
def degreeOneProjection (b : Module.Basis I R L) : U →ₗ[R] L :=
  (Finsupp.linearCombination R (fun xs : OrderedWord I =>
    match xs.val with
    | [i] => b i
    | _ => 0)).comp (pbwCoordinates b)

theorem degreeOneProjection_comp_ι (b : Module.Basis I R L) :
    (degreeOneProjection b).comp (UniversalEnvelopingAlgebra.ι R).toLinearMap =
      LinearMap.id := by
  apply b.ext
  intro i
  have hword : UniversalEnvelopingAlgebra.ι R (b i) = basisWord b [i] := by
    simp only [basisWord_cons, basisWord_nil, mul_one]
  let xs : OrderedWord I := ⟨[i], by simp⟩
  change Finsupp.linearCombination R (fun ys : OrderedWord I =>
      match ys.val with
      | [j] => b j
      | _ => 0) (pbwCoordinates b (UniversalEnvelopingAlgebra.ι R (b i))) = b i
  rw [hword, pbwCoordinates_basisWord]
  change Finsupp.linearCombination R _ (normalize b xs.val) = b i
  rw [normalize_ordered b xs, Finsupp.linearCombination_single, one_smul]

/-- For a commutative ring R and an R-Lie algebra L with
ordered R-basis b, the canonical Lie map ι : L → U_R(L) is
injective. Its underlying R-linear map has the length-one PBW
coordinate projection as a left inverse. -/
theorem ι_injective_of_basis (b : Module.Basis I R L) :
    Function.Injective (UniversalEnvelopingAlgebra.ι R (L := L)) := by
  intro x y hxy
  have hx := LinearMap.congr_fun (degreeOneProjection_comp_ι b) x
  have hy := LinearMap.congr_fun (degreeOneProjection_comp_ι b) y
  have h := congrArg (degreeOneProjection b) hxy
  exact hx.symm.trans (h.trans hy)

theorem ι_injective_of_free [Module.Free R L] :
    Function.Injective (UniversalEnvelopingAlgebra.ι R (L := L)) := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) := linearOrderOfSTO WellOrderingRel
  exact ι_injective_of_basis (Module.Free.chooseBasis R L)

end UniversalEnvelopingAlgebra.PBW
