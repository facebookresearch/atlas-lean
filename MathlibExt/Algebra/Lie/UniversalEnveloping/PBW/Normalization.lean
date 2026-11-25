/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Data.List.AdjacentInversion
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Filtration
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-!
# Constructive ordered-word reduction in the native enveloping algebra

The normalizer searches for the first adjacent inversion and uses the actual
basis coordinates of the Lie bracket. Its recursion terminates by the weight
of the original word. Evaluating the result in the native quotient recovers
the original word, giving the spanning half of ordered-word PBW over every
commutative ring and an arbitrary basis.

Confluence, independence and a PBW basis are separate conclusions. This
module does not assert them.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Weakly increasing finite words in an arbitrary ordered alphabet. -/
@[implicit_reducible]
def OrderedWord (I : Type w) [LinearOrder I] :=
  {xs : List I // xs.Pairwise (· ≤ ·)}

/-- An actual word in the selected basis, evaluated in the native quotient. -/
def basisWord (b : Module.Basis I R L) (xs : List I) : U :=
  word R L (xs.map b)

omit [LinearOrder I] in
@[simp]
theorem basisWord_nil (b : Module.Basis I R L) : basisWord b [] = 1 := rfl

omit [LinearOrder I] in
@[simp]
theorem basisWord_cons (b : Module.Basis I R L) (i : I) (xs : List I) :
    basisWord b (i :: xs) = UniversalEnvelopingAlgebra.ι R (b i) * basisWord b xs := rfl

omit [LinearOrder I] in
@[simp]
theorem basisWord_append (b : Module.Basis I R L) (xs ys : List I) :
    basisWord b (xs ++ ys) = basisWord b xs * basisWord b ys := by
  simp only [basisWord, List.map_append, word_append]

/-- Evaluate a weakly increasing word in the original quotient. -/
def orderedWordValue (b : Module.Basis I R L) (xs : OrderedWord I) : U :=
  basisWord b xs.val

/-- Linear evaluation of finite combinations of weakly increasing words. -/
def orderedWordLinear (b : Module.Basis I R L) : (OrderedWord I →₀ R) →ₗ[R] U :=
  Finsupp.linearCombination R (orderedWordValue b)

@[simp]
theorem orderedWordLinear_single (b : Module.Basis I R L) (xs : OrderedWord I) (r : R) :
    orderedWordLinear b (Finsupp.single xs r) = r • orderedWordValue b xs := by
  simp only [orderedWordLinear, Finsupp.linearCombination_single]

/-- Terminating reduction to finite combinations of ordered words. All
coefficients of a contraction are the actual bracket coordinates of `b`. -/
def normalize (b : Module.Basis I R L) (xs : List I) : OrderedWord I →₀ R :=
  match h : List.adjacentInversion xs with
  | none =>
      Finsupp.single
        ⟨xs, List.pairwise_le_of_adjacentInversion_eq_none xs h⟩ 1
  | some (p, i, j, s) =>
      normalize b (p ++ j :: i :: s) +
        (b.repr ⁅b i, b j⁆).sum
          (fun k r => r • normalize b (p ++ k :: s))
termination_by List.inversionWeight xs
decreasing_by
  all_goals
    have hs := List.adjacentInversion_spec xs p i j s h
    rw [hs.1]
  · exact List.inversionWeight_adjacent_swap_lt p i j s hs.2
  · exact List.inversionWeight_contract_lt p i j _ s

theorem normalize_of_adjacentInversion (b : Module.Basis I R L)
    {xs p s : List I} {i j : I}
    (h : List.adjacentInversion xs = some (p, i, j, s)) :
    normalize b xs =
      normalize b (p ++ j :: i :: s) +
        (b.repr ⁅b i, b j⁆).sum
          (fun k r => r • normalize b (p ++ k :: s)) := by
  rw [normalize]
  split
  · rename_i hn
    rw [h] at hn
    cases hn
  · rename_i p' i' j' s' hs
    have ht : (p', i', j', s') = (p, i, j, s) := Option.some.inj (hs.symm.trans h)
    cases ht
    rfl

/-- The normalizer fixes every original weakly increasing word. -/
theorem normalize_ordered (b : Module.Basis I R L) (xs : OrderedWord I) :
    normalize b xs.val = Finsupp.single xs 1 := by
  have h := List.adjacentInversion_eq_none_of_pairwise_le xs.val xs.property
  rw [normalize]
  split
  · rfl
  · rename_i p i j s hs
    rw [h] at hs
    cases hs

/-- Insert a vector between fixed basis words. This map is linear in that
vector over the original commutative scalar ring. -/
def insertGenerator (b : Module.Basis I R L) (p s : List I) : L →ₗ[R] U where
  toFun x := basisWord b p * UniversalEnvelopingAlgebra.ι R x * basisWord b s
  map_add' x y := by
    simp only [map_add, mul_add, add_mul]
  map_smul' r x := by
    simp only [map_smul, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

omit [LinearOrder I] in
@[simp]
theorem insertGenerator_apply (b : Module.Basis I R L) (p s : List I) (x : L) :
    insertGenerator b p s x =
      basisWord b p * UniversalEnvelopingAlgebra.ι R x * basisWord b s := rfl

omit [LinearOrder I] in
theorem insertGenerator_basis (b : Module.Basis I R L) (p s : List I) (i : I) :
    insertGenerator b p s (b i) = basisWord b (p ++ i :: s) := by
  simp only [insertGenerator_apply, basisWord_append, basisWord_cons, mul_assoc]

omit [LinearOrder I] in
/-- Expanding a bracket uses the basis's finite, literal coordinate sum. -/
theorem insertGenerator_bracket (b : Module.Basis I R L)
    (p s : List I) (i j : I) :
    (b.repr ⁅b i, b j⁆).sum
        (fun k r => r • basisWord b (p ++ k :: s)) =
      insertGenerator b p s ⁅b i, b j⁆ := by
  have h := congrArg (fun x : L => insertGenerator b p s x) (b.linearCombination_repr ⁅b i, b j⁆)
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    insertGenerator_basis] using h

omit [LinearOrder I] in
/-- The elementary reduction is an equality in the actual native quotient;
this theorem has no order premise because the quotient relation is universal. -/
theorem basisWord_adjacent_rule (b : Module.Basis I R L)
    (p s : List I) (i j : I) :
    basisWord b (p ++ i :: j :: s) =
      basisWord b (p ++ j :: i :: s) +
        (b.repr ⁅b i, b j⁆).sum
          (fun k r => r • basisWord b (p ++ k :: s)) := by
  rw [insertGenerator_bracket]
  have hrel := ι_mul_sub_mul_ι R L (b i) (b j)
  have hxy :
      UniversalEnvelopingAlgebra.ι R (b i) * UniversalEnvelopingAlgebra.ι R (b j) =
        UniversalEnvelopingAlgebra.ι R (b j) * UniversalEnvelopingAlgebra.ι R (b i) +
          UniversalEnvelopingAlgebra.ι R ⁅b i, b j⁆ :=
    (sub_eq_iff_eq_add.mp hrel).trans (add_comm _ _)
  have h := congrArg (fun a : U => basisWord b p * a * basisWord b s) hxy
  simpa only [basisWord_append, basisWord_cons, insertGenerator_apply,
    mul_add, add_mul, mul_assoc] using h

/-- Every reduction computes the original word in the native enveloping
algebra. This proves spanning without assuming confluence or independence. -/
theorem orderedWordLinear_normalize (b : Module.Basis I R L) (xs : List I) :
    orderedWordLinear b (normalize b xs) = basisWord b xs := by
  generalize hn : List.inversionWeight xs = n
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
      cases hr : List.adjacentInversion xs with
      | none =>
          have hordered : normalize b xs =
              Finsupp.single (⟨xs, List.pairwise_le_of_adjacentInversion_eq_none xs hr⟩ : OrderedWord I) 1 :=
            normalize_ordered b ⟨xs, List.pairwise_le_of_adjacentInversion_eq_none xs hr⟩
          rw [hordered, orderedWordLinear_single]
          simp only [one_smul, orderedWordValue]
      | some t =>
          rcases t with ⟨p, i, j, s⟩
          obtain ⟨hxs, hji⟩ := List.adjacentInversion_spec xs p i j s hr
          have hswap : List.inversionWeight (p ++ j :: i :: s) < n := by
            rw [← hn, hxs]
            exact List.inversionWeight_adjacent_swap_lt p i j s hji
          have hswapEval := ih (List.inversionWeight (p ++ j :: i :: s))
            hswap (p ++ j :: i :: s) rfl
          have hcontractEval (k : I) :
              orderedWordLinear b (normalize b (p ++ k :: s)) =
                basisWord b (p ++ k :: s) := by
            apply ih (List.inversionWeight (p ++ k :: s)) ?_ (p ++ k :: s) rfl
            rw [← hn, hxs]
            exact List.inversionWeight_contract_lt p i j k s
          rw [normalize_of_adjacentInversion b hr, map_add, hswapEval]
          have hsum :
              orderedWordLinear b ((b.repr ⁅b i, b j⁆).sum
                (fun k r => r • normalize b (p ++ k :: s))) =
              (b.repr ⁅b i, b j⁆).sum
                (fun k r => r • basisWord b (p ++ k :: s)) := by
            simp only [Finsupp.sum, map_sum, map_smul]
            apply Finset.sum_congr rfl
            intro k hk
            rw [hcontractEval]
          rw [hsum, hxs]
          exact (basisWord_adjacent_rule b p s i j).symm

/-- All weakly increasing words span the actual native enveloping algebra
for every selected basis, including infinite bases and positive characteristic. -/
theorem orderedWord_spanning (b : Module.Basis I R L) :
    Submodule.span R (Set.range (orderedWordValue b)) = ⊤ := by
  let S : Submodule R U := Submodule.span R (Set.range (orderedWordValue b))
  have hword (xs : List I) : basisWord b xs ∈ S := by
    rw [← orderedWordLinear_normalize b xs]
    change orderedWordLinear b (normalize b xs) ∈
      Submodule.span R (Set.range (orderedWordValue b))
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self (orderedWordLinear b) (normalize b xs)
  have hmul {a c : U} (ha : a ∈ S) (hc : c ∈ S) : a * c ∈ S := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨xs, rfl⟩ := ha
        induction hc using Submodule.span_induction with
        | mem c hc =>
            obtain ⟨ys, rfl⟩ := hc
            change basisWord b xs.val * basisWord b ys.val ∈ S
            rw [← basisWord_append]
            exact hword (xs.val ++ ys.val)
        | zero => simpa only [mul_zero] using S.zero_mem
        | add c d hc hd ihc ihd =>
            rw [mul_add]
            exact S.add_mem ihc ihd
        | smul r c hc ih =>
            rw [mul_smul_comm]
            exact S.smul_mem r ih
    | zero => simpa only [zero_mul] using S.zero_mem
    | add a c ha hc iha ihc =>
        rw [add_mul]
        exact S.add_mem iha ihc
    | smul r a ha ih =>
        rw [smul_mul_assoc]
        exact S.smul_mem r ih
  have hι (x : L) : UniversalEnvelopingAlgebra.ι R x ∈ S := by
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
    simp only [Finsupp.sum, map_sum, map_smul]
    apply S.sum_mem
    intro i hi
    exact S.smul_mem _ (by
      simpa only [basisWord_cons, basisWord_nil, mul_one] using hword [i])
  apply eq_top_iff.mpr
  intro a ha
  clear ha
  change a ∈ S
  induction a using UniversalEnvelopingAlgebra.induction R L with
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact S.smul_mem r (by simpa only [basisWord_nil] using hword [])
  | ι x => exact hι x
  | mul a c ha hc => exact hmul ha hc
  | add a c ha hc => exact S.add_mem ha hc

end UniversalEnvelopingAlgebra.PBW
