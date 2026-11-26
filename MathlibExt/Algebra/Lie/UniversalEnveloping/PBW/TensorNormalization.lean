/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.Confluence
public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.CriticalPairs
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Linear tensor normalization and contextual Lie relations

Let `R` be a commutative ring and `b : I → L` a Lie-algebra basis indexed by a linearly
ordered alphabet. The tensor-algebra basis is indexed by free-monoid words in `I`. Extending
ordered-word normalization linearly through this basis gives `T_R(L) →ₗ[R] (OrderedWord I →₀
R)`.

Normalization of one or two inserted Lie vectors agrees with the corresponding linear or
bilinear basis-coordinate insertion. The adjacent relation identities imply that this linear
normalizer kills `p(τ(x)τ(y)-τ(y)τ(x)-τ([x,y]))s` for arbitrary left and right tensor factors.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "T" => TensorAlgebra R L
local notation "N" => (OrderedWord I →₀ R)
local notation "τ" => TensorAlgebra.ι R

omit [LinearOrder I] in
private theorem freeAlgebra_basisFreeMonoid_ofList (xs : List I) :
    FreeAlgebra.basisFreeMonoid R I (FreeMonoid.ofList xs) =
      (xs.map (FreeAlgebra.ι R)).prod := by
  rw [FreeAlgebra.basisFreeMonoid, Module.Basis.map_apply]
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := I)).symm
    ((MonoidAlgebra.coeffLinearEquiv R).symm (Finsupp.single (FreeMonoid.ofList xs) 1)) = _
  have hc : (MonoidAlgebra.coeffLinearEquiv R).symm
      (Finsupp.single (FreeMonoid.ofList xs) (1 : R)) =
      MonoidAlgebra.of R (FreeMonoid I) (FreeMonoid.ofList xs) := rfl
  rw [hc]
  change MonoidAlgebra.lift R (FreeAlgebra R I) (FreeMonoid I)
    (FreeMonoid.lift (FreeAlgebra.ι R))
      (MonoidAlgebra.of R (FreeMonoid I) (FreeMonoid.ofList xs)) = _
  rw [MonoidAlgebra.lift_of, FreeMonoid.lift_ofList]

/-- The tensor-algebra value of a Lie basis word.

Map a list of basis indices to the tensor generators `τ(b_i)` and multiply them in list order. -/
def tensorWord (b : Module.Basis I R L) (xs : List I) : T :=
  (xs.map (fun i => τ (b i))).prod

omit [LinearOrder I] in
/-- The tensor-algebra value of the empty basis word.

The empty word evaluates to the tensor-algebra unit. -/
@[simp]
theorem tensorWord_nil (b : Module.Basis I R L) : tensorWord b [] = 1 := rfl

omit [LinearOrder I] in
/-- The tensor-algebra value after adjoining a first basis letter.

The word `i :: xs` evaluates to `τ(b_i)` times the tensor word of `xs`. -/
@[simp]
theorem tensorWord_cons (b : Module.Basis I R L) (i : I) (xs : List I) :
    tensorWord b (i :: xs) = τ (b i) * tensorWord b xs := rfl

omit [LinearOrder I] in
/-- The tensor-algebra value of concatenated basis words.

The tensor word of `xs ++ ys` equals the product of their tensor words in that order. -/
@[simp]
theorem tensorWord_append (b : Module.Basis I R L) (xs ys : List I) :
    tensorWord b (xs ++ ys) = tensorWord b xs * tensorWord b ys := by
  simp only [tensorWord, List.map_append, List.prod_append]

omit [LinearOrder I] in
/-- The tensor basis element indexed by a list.

The tensor-algebra basis element at the free-monoid word of `xs` equals the tensor product of
its basis generators. -/
theorem tensorBasis_ofList (b : Module.Basis I R L) (xs : List I) :
    b.tensorAlgebra (FreeMonoid.ofList xs) = tensorWord b xs := by
  rw [Module.Basis.tensorAlgebra, Module.Basis.map_apply,
    freeAlgebra_basisFreeMonoid_ofList]
  apply (TensorAlgebra.equivFreeAlgebra b).injective
  change (TensorAlgebra.equivFreeAlgebra b)
      ((TensorAlgebra.equivFreeAlgebra b).symm ((xs.map (FreeAlgebra.ι R)).prod)) = _
  rw [AlgEquiv.apply_symm_apply]
  simp only [tensorWord, map_list_prod, List.map_map,
    TensorAlgebra.equivFreeAlgebra_ι_apply, Function.comp_def]

omit [LinearOrder I] in
/-- The word formula for a tensor-algebra basis index.

The tensor basis element indexed by `xs : FreeMonoid I` is the tensor word of `xs.toList`. -/
theorem tensorBasis_apply (b : Module.Basis I R L) (xs : FreeMonoid I) :
    b.tensorAlgebra xs = tensorWord b xs.toList := by
  simpa only [FreeMonoid.ofList_toList] using tensorBasis_ofList b xs.toList

/-- The linear tensor-algebra extension of ordered-word normalization.

Expand a tensor-algebra element in the free-monoid basis and evaluate the same finite
coefficients on the ordered normal forms of its word indices. -/
def tensorNormalizer (b : Module.Basis I R L) : T →ₗ[R] N :=
  (Finsupp.linearCombination R (fun xs : FreeMonoid I => normalize b xs.toList)).comp
    b.tensorAlgebra.repr.toLinearMap

/-- The normalizer on a tensor basis word.

The linear tensor normalizer sends the tensor word of `xs` to the ordered normal form
`normalize(xs)`. -/
@[simp]
theorem tensorNormalizer_tensorWord (b : Module.Basis I R L) (xs : List I) :
    tensorNormalizer b (tensorWord b xs) = normalize b xs := by
  rw [← tensorBasis_ofList]
  change (Finsupp.linearCombination R (fun ys : FreeMonoid I => normalize b ys.toList))
    (b.tensorAlgebra.repr (b.tensorAlgebra (FreeMonoid.ofList xs))) = _
  rw [b.tensorAlgebra.repr_self, Finsupp.linearCombination_single,
    FreeMonoid.toList_ofList, one_smul]

/-- The tensor insertion of a Lie vector in a basis-word context.

For fixed prefix and suffix words, insert `τ(x)` between their tensor-algebra products. -/
def tensorInsertion (b : Module.Basis I R L) (p s : List I) : L →ₗ[R] T :=
  (tensorContext R L (tensorWord b p) (tensorWord b s)).comp τ

omit [LinearOrder I] in
/-- The value of a contextual tensor insertion.

The insertion map sends `x` to `tensorWord(p) * τ(x) * tensorWord(s)`. -/
@[simp]
theorem tensorInsertion_apply (b : Module.Basis I R L) (p s : List I) (x : L) :
    tensorInsertion b p s x = tensorWord b p * τ x * tensorWord b s := rfl

/-- The normalized value of a one-vector tensor insertion.

Applying the linear tensor normalizer to an inserted vector equals its basis-coordinate
normalization insertion. -/
theorem tensorNormalizer_tensorInsertion (b : Module.Basis I R L)
    (p s : List I) (x : L) :
    tensorNormalizer b (tensorWord b p * τ x * tensorWord b s) =
      normalizationInsertion b p s x := by
  have h : (tensorNormalizer b).comp (tensorInsertion b p s) =
      normalizationInsertion b p s := by
    apply b.ext
    intro i
    change tensorNormalizer b (tensorWord b p * τ (b i) * tensorWord b s) = _
    have hw : tensorWord b p * τ (b i) * tensorWord b s =
        tensorWord b (p ++ i :: s) := by
      simp only [tensorWord_append, tensorWord_cons, mul_assoc]
    rw [hw, tensorNormalizer_tensorWord, normalizationInsertion_basis]
  exact LinearMap.congr_fun h x

private def normalizedTensorPair (b : Module.Basis I R L) (p s : List I) :
    L →ₗ[R] L →ₗ[R] N where
  toFun x :=
    { toFun := fun y => tensorNormalizer b (tensorWord b p * τ x * τ y * tensorWord b s)
      map_add' := fun y z => by
        simp only [map_add, mul_add, add_mul]
      map_smul' := fun r y => by
        simp only [map_smul, mul_smul_comm, smul_mul_assoc, RingHom.id_apply] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change tensorNormalizer b (tensorWord b p * τ (x + y) * τ z * tensorWord b s) =
      tensorNormalizer b (tensorWord b p * τ x * τ z * tensorWord b s) +
        tensorNormalizer b (tensorWord b p * τ y * τ z * tensorWord b s)
    simp only [LinearMap.add_apply, map_add, mul_add, add_mul]
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    change tensorNormalizer b (tensorWord b p * τ (r • x) * τ y * tensorWord b s) =
      (RingHom.id R) r • tensorNormalizer b (tensorWord b p * τ x * τ y * tensorWord b s)
    simp only [LinearMap.smul_apply, map_smul, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

/-- The normalized value of an adjacent tensor-vector pair.

Applying the linear tensor normalizer to two inserted Lie vectors equals the bilinear
normalization pair in the same prefix and suffix. -/
theorem tensorNormalizer_tensorPair (b : Module.Basis I R L)
    (p s : List I) (x y : L) :
    tensorNormalizer b (tensorWord b p * τ x * τ y * tensorWord b s) =
      normalizationPair b p s x y := by
  have h : normalizedTensorPair b p s = normalizationPair b p s := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change tensorNormalizer b
      (tensorWord b p * τ (b i) * τ (b j) * tensorWord b s) = _
    have hw : tensorWord b p * τ (b i) * τ (b j) * tensorWord b s =
        tensorWord b (p ++ i :: j :: s) := by
      simp only [tensorWord_append, tensorWord_cons, mul_assoc]
    rw [hw, tensorNormalizer_tensorWord,
      normalizationPair_basis_left, normalizationInsertion_basis]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- Annihilation of a Lie relation in basis-word tensor contexts.

The tensor normalizer kills a defining Lie relation multiplied on the left and right by tensor
basis words. -/
theorem tensorNormalizer_word_relationError (b : Module.Basis I R L)
    (p s : List I) (x y : L) :
    tensorNormalizer b (tensorWord b p * relationError R L x y * tensorWord b s) = 0 := by
  simp only [relationError, mul_sub, sub_mul, map_sub]
  simp only [← mul_assoc]
  rw [tensorNormalizer_tensorPair, tensorNormalizer_tensorPair,
    tensorNormalizer_tensorInsertion, normalizationPair_commutator, sub_self]

private def normalizedErrorSandwich (b : Module.Basis I R L) (x y : L) :
    T →ₗ[R] T →ₗ[R] N where
  toFun p :=
    { toFun := fun s => tensorNormalizer b (p * relationError R L x y * s)
      map_add' := fun s t => by rw [mul_add, map_add]
      map_smul' := fun r s => by rw [mul_smul_comm, map_smul]; simp only [RingHom.id_apply] }
  map_add' p q := by
    apply LinearMap.ext
    intro s
    change tensorNormalizer b ((p + q) * relationError R L x y * s) =
      tensorNormalizer b (p * relationError R L x y * s) +
        tensorNormalizer b (q * relationError R L x y * s)
    simp only [LinearMap.add_apply, add_mul, map_add]
  map_smul' r p := by
    apply LinearMap.ext
    intro s
    change tensorNormalizer b ((r • p) * relationError R L x y * s) =
      (RingHom.id R) r • tensorNormalizer b (p * relationError R L x y * s)
    simp only [LinearMap.smul_apply, smul_mul_assoc, map_smul, RingHom.id_apply]

/-- Annihilation of every contextual tensor Lie relation.

For arbitrary `p,s ∈ T_R(L)` and `x,y ∈ L`, the linear normalizer sends `p * r(x,y) * s` to
zero. -/
theorem tensorNormalizer_relationError (b : Module.Basis I R L)
    (p s : T) (x y : L) :
    tensorNormalizer b (p * relationError R L x y * s) = 0 := by
  have h : normalizedErrorSandwich b x y = 0 := by
    apply b.tensorAlgebra.ext
    intro p
    apply b.tensorAlgebra.ext
    intro s
    change tensorNormalizer b
      (b.tensorAlgebra p * relationError R L x y * b.tensorAlgebra s) = 0
    rw [tensorBasis_apply, tensorBasis_apply]
    exact tensorNormalizer_word_relationError b p.toList s.toList x y
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) s

end UniversalEnvelopingAlgebra.PBW
