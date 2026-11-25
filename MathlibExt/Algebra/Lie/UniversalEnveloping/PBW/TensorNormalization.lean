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
# Linear tensor normalization and the actual contextual Lie relations

The native tensor basis identifies its words with free-monoid words.
Normalization extends linearly through that basis. The actual adjacent-word
invariance then annihilates every contextual Lie relation, first on basis
words and then on arbitrary tensor factors by bilinear extension.
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

/-- An actual basis word in the original tensor algebra. -/
def tensorWord (b : Module.Basis I R L) (xs : List I) : T :=
  (xs.map (fun i => τ (b i))).prod

omit [LinearOrder I] in
@[simp]
theorem tensorWord_nil (b : Module.Basis I R L) : tensorWord b [] = 1 := rfl

omit [LinearOrder I] in
@[simp]
theorem tensorWord_cons (b : Module.Basis I R L) (i : I) (xs : List I) :
    tensorWord b (i :: xs) = τ (b i) * tensorWord b xs := rfl

omit [LinearOrder I] in
@[simp]
theorem tensorWord_append (b : Module.Basis I R L) (xs ys : List I) :
    tensorWord b (xs ++ ys) = tensorWord b xs * tensorWord b ys := by
  simp only [tensorWord, List.map_append, List.prod_append]

omit [LinearOrder I] in
/-- The native tensor basis evaluates its free-monoid index as the actual
product of the original basis vectors. -/
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
theorem tensorBasis_apply (b : Module.Basis I R L) (xs : FreeMonoid I) :
    b.tensorAlgebra xs = tensorWord b xs.toList := by
  simpa only [FreeMonoid.ofList_toList] using tensorBasis_ofList b xs.toList

/-- Extend the actual recursive normalizer through the native tensor basis. -/
def tensorNormalizer (b : Module.Basis I R L) : T →ₗ[R] N :=
  (Finsupp.linearCombination R (fun xs : FreeMonoid I => normalize b xs.toList)).comp
    b.tensorAlgebra.repr.toLinearMap

@[simp]
theorem tensorNormalizer_tensorWord (b : Module.Basis I R L) (xs : List I) :
    tensorNormalizer b (tensorWord b xs) = normalize b xs := by
  rw [← tensorBasis_ofList]
  change (Finsupp.linearCombination R (fun ys : FreeMonoid I => normalize b ys.toList))
    (b.tensorAlgebra.repr (b.tensorAlgebra (FreeMonoid.ofList xs))) = _
  rw [b.tensorAlgebra.repr_self, Finsupp.linearCombination_single,
    FreeMonoid.toList_ofList, one_smul]

/-- Single-vector insertion in the actual tensor algebra. -/
def tensorInsertion (b : Module.Basis I R L) (p s : List I) : L →ₗ[R] T :=
  (tensorContext R L (tensorWord b p) (tensorWord b s)).comp τ

omit [LinearOrder I] in
@[simp]
theorem tensorInsertion_apply (b : Module.Basis I R L) (p s : List I) (x : L) :
    tensorInsertion b p s x = tensorWord b p * τ x * tensorWord b s := rfl

/-- The linear tensor normalizer agrees with its actual basis-coordinate
insertion on every vector. -/
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

/-- Two-vector tensor insertion gives the same bilinear normalization context. -/
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

/-- Every actual defining Lie relation in basis-word contexts is annihilated. -/
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

/-- Every contextual native Lie relation is annihilated for arbitrary tensor
factors, using the actual native tensor basis in both factors. -/
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
