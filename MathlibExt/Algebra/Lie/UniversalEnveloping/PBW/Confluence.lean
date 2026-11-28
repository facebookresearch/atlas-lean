/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.NormalizationContexts
public import Mathlib.Tactic.Abel

/-!
# Normal forms preserve every contextual Lie commutator

Let R be a commutative ring and L an R-Lie algebra with basis b indexed
by a linearly ordered type I. The ordered-word normal form takes values
in OrderedWord(I) →₀ R. For a prefix p, suffix s and x ∈ L, insertion
means the finite basis expansion
Ins_(p,s)(x) = ∑_i (b.repr(x))_i Norm(p ++ [i] ++ s).

For every adjacent inversion i > j, normalization satisfies
Norm(p ++ [i,j] ++ s) =
Norm(p ++ [j,i] ++ s) + Ins_(p,s)([b_i,b_j]).
The relation holds for any chosen inverted pair. By skew-symmetry
it gives the commutator identity in all index orientations; bilinear
basis expansion gives the corresponding identity for arbitrary
inserted vectors x,y ∈ L.

The weight of a word is a_(length)+its inversion count, with
a_0 = 0 and a_(n+1) = a_n+n²+1. It decreases under an inverted
adjacent swap and under replacement of two letters by one bracket
letter. Disjoint reductions agree, and the difference for overlapping
reductions is an insertion of the Jacobi identity.
All coefficient, Lie-carrier and basis-index worlds are independent.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "N" => (OrderedWord I →₀ R)

private theorem normalizationPair_basis (b : Module.Basis I R L)
    (p s : List I) (i j : I) :
    normalizationPair b p s (b i) (b j) = normalize b (p ++ i :: j :: s) := by
  rw [normalizationPair_basis_left, normalizationInsertion_basis]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

private def bracketInsertion (b : Module.Basis I R L) (p s : List I) :
    L →ₗ[R] L →ₗ[R] N where
  toFun x :=
    { toFun := fun y => normalizationInsertion b p s ⁅x, y⁆
      map_add' := fun y z => by rw [lie_add, map_add]
      map_smul' := fun r y => by rw [lie_smul, map_smul]; simp only [RingHom.id_apply] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change normalizationInsertion b p s ⁅x + y, z⁆ =
      normalizationInsertion b p s ⁅x, z⁆ + normalizationInsertion b p s ⁅y, z⁆
    simp only [add_lie, map_add, LinearMap.add_apply]
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    change normalizationInsertion b p s ⁅r • x, y⁆ =
      (RingHom.id R) r • normalizationInsertion b p s ⁅x, y⁆
    simp only [smul_lie, map_smul, LinearMap.smul_apply, RingHom.id_apply]

private theorem pair_commutator_of_basis_identities (b : Module.Basis I R L)
    (p s : List I)
    (h : ∀ i j : I,
      normalize b (p ++ i :: j :: s) - normalize b (p ++ j :: i :: s) =
        normalizationInsertion b p s ⁅b i, b j⁆)
    (x y : L) :
    normalizationPair b p s x y - normalizationPair b p s y x =
      normalizationInsertion b p s ⁅x, y⁆ := by
  have heq : normalizationPair b p s =
      (normalizationPair b p s).flip + bracketInsertion b p s := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change normalizationPair b p s (b i) (b j) =
      normalizationPair b p s (b j) (b i) + normalizationInsertion b p s ⁅b i, b j⁆
    rw [normalizationPair_basis, normalizationPair_basis]
    exact (sub_eq_iff_eq_add.mp (h i j)).trans (add_comm _ _)
  have hxy := LinearMap.congr_fun (LinearMap.congr_fun heq x) y
  change normalizationPair b p s x y =
    normalizationPair b p s y x + normalizationInsertion b p s ⁅x, y⁆ at hxy
  exact sub_eq_iff_eq_add.mpr (hxy.trans (add_comm _ _))

/-- Let R be a commutative ring, L an R-Lie algebra and b an
ordered R-basis. Fix a word xs and assume the adjacent-inversion
normalization relation for every word of smaller weight
a_(length)+inversionCount, where a_0 = 0 and a_(n+1) = a_n+n²+1.
For prefixes p and suffixes s with |p|+2+|s| < |xs|, and x,y ∈ L,
the bilinear normal-form pair satisfies
Pair_(p,s)(x,y)−Pair_(p,s)(y,x) = Ins_(p,s)([x,y]).
The pair and insertion maps use finite expansion in b. -/
private theorem pair_commutator_of_smaller_reductions
    (b : Module.Basis I R L) (xs : List I)
    (hsmall : ∀ (p : List I) (i j : I) (s : List I), j < i →
      List.inversionWeight (p ++ i :: j :: s) < List.inversionWeight xs →
        normalize b (p ++ i :: j :: s) = reductionValue b p i j s)
    (p s : List I) (hlen : p.length + 2 + s.length < xs.length)
    (x y : L) :
    normalizationPair b p s x y - normalizationPair b p s y x =
      normalizationInsertion b p s ⁅x, y⁆ := by
  apply pair_commutator_of_basis_identities b p s
  intro i j
  rcases lt_trichotomy j i with hji | hji | hij
  · have hw : List.inversionWeight (p ++ i :: j :: s) < List.inversionWeight xs :=
      List.inversionWeight_lt_of_length_lt (by
        simp only [List.length_append, List.length_cons]
        omega)
    have h := hsmall p i j s hji hw
    rw [reductionValue] at h
    rw [h]
    abel
  · subst j
    simp only [sub_self, lie_self, map_zero]
  · have hw : List.inversionWeight (p ++ j :: i :: s) < List.inversionWeight xs :=
      List.inversionWeight_lt_of_length_lt (by
        simp only [List.length_append, List.length_cons]
        omega)
    have h := hsmall p j i s hij hw
    rw [reductionValue] at h
    rw [h, ← lie_skew (b i) (b j), map_neg]
    abel

private theorem reductionValue_overlap_eq
    (b : Module.Basis I R L) (p s : List I) (i j k : I)
    (hji : j < i) (hkj : k < j)
    (hsmall : ∀ (q : List I) (a c : I) (t : List I), c < a →
      List.inversionWeight (q ++ a :: c :: t) <
          List.inversionWeight (p ++ i :: j :: k :: s) →
        normalize b (q ++ a :: c :: t) = reductionValue b q a c t) :
    reductionValue b p i j (k :: s) = reductionValue b (p ++ [i]) j k s := by
  have hki : k < i := hkj.trans hji
  have hleft : List.inversionWeight (p ++ j :: i :: k :: s) <
      List.inversionWeight (p ++ i :: j :: k :: s) :=
    List.inversionWeight_adjacent_swap_lt p i j (k :: s) hji
  have hright : List.inversionWeight (p ++ i :: k :: j :: s) <
      List.inversionWeight (p ++ i :: j :: k :: s) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      List.inversionWeight_adjacent_swap_lt (p ++ [i]) j k s hkj
  have hleft₂ : List.inversionWeight (p ++ j :: k :: i :: s) <
      List.inversionWeight (p ++ i :: j :: k :: s) := by
    have hstep := List.inversionWeight_adjacent_swap_lt (p ++ [j]) i k s hki
    have hstep' : List.inversionWeight (p ++ j :: k :: i :: s) <
        List.inversionWeight (p ++ j :: i :: k :: s) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hstep
    exact hstep'.trans hleft
  have hright₂ : List.inversionWeight (p ++ k :: i :: j :: s) <
      List.inversionWeight (p ++ i :: j :: k :: s) :=
    (List.inversionWeight_adjacent_swap_lt p i k (j :: s) hki).trans hright
  have hA : normalize b (p ++ j :: i :: k :: s) =
      normalize b (p ++ j :: k :: i :: s) +
        normalizationInsertion b (p ++ [j]) s ⁅b i, b k⁆ := by
    have h := hsmall (p ++ [j]) i k s hki (by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hleft)
    simpa only [reductionValue, List.append_assoc, List.cons_append, List.nil_append] using h
  have hA₂ : normalize b (p ++ j :: k :: i :: s) =
      normalize b (p ++ k :: j :: i :: s) +
        normalizationInsertion b p (i :: s) ⁅b j, b k⁆ := by
    simpa only [reductionValue] using hsmall p j k (i :: s) hkj hleft₂
  have hB : normalize b (p ++ i :: k :: j :: s) =
      normalize b (p ++ k :: i :: j :: s) +
        normalizationInsertion b p (j :: s) ⁅b i, b k⁆ := by
    simpa only [reductionValue] using hsmall p i k (j :: s) hki hright
  have hB₂ : normalize b (p ++ k :: i :: j :: s) =
      normalize b (p ++ k :: j :: i :: s) +
        normalizationInsertion b (p ++ [k]) s ⁅b i, b j⁆ := by
    have h := hsmall (p ++ [k]) i j s hji (by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hright₂)
    simpa only [reductionValue, List.append_assoc, List.cons_append, List.nil_append] using h
  have hcomm := pair_commutator_of_smaller_reductions b (p ++ i :: j :: k :: s)
    hsmall p s (by simp only [List.length_append, List.length_cons]; omega)
  let F := normalizationPair b p s
  let G := normalizationInsertion b p s
  have h₁ : F ⁅b j, b k⁆ (b i) - F (b i) ⁅b j, b k⁆ = G ⁅⁅b j, b k⁆, b i⁆ :=
    hcomm ⁅b j, b k⁆ (b i)
  have h₂ : F (b j) ⁅b i, b k⁆ - F ⁅b i, b k⁆ (b j) = G ⁅b j, ⁅b i, b k⁆⁆ :=
    hcomm (b j) ⁅b i, b k⁆
  have h₃ : F ⁅b i, b j⁆ (b k) - F (b k) ⁅b i, b j⁆ = G ⁅⁅b i, b j⁆, b k⁆ :=
    hcomm ⁅b i, b j⁆ (b k)
  have hj : ⁅⁅b j, b k⁆, b i⁆ + ⁅b j, ⁅b i, b k⁆⁆ + ⁅⁅b i, b j⁆, b k⁆ = 0 := by
    rw [← lie_skew ⁅b j, b k⁆ (b i), leibniz_lie (b i) (b j) (b k)]
    abel
  have hsum :
      (F ⁅b j, b k⁆ (b i) - F (b i) ⁅b j, b k⁆) +
        (F (b j) ⁅b i, b k⁆ - F ⁅b i, b k⁆ (b j)) +
          (F ⁅b i, b j⁆ (b k) - F (b k) ⁅b i, b j⁆) = 0 := by
    rw [h₁, h₂, h₃, ← map_add, ← map_add, hj, map_zero]
  rw [reductionValue, reductionValue]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hA, hA₂, hB, hB₂]
  simp only [← normalizationPair_basis_left, ← normalizationPair_basis_right]
  apply sub_eq_zero.mp
  calc
    _ = (F ⁅b j, b k⁆ (b i) - F (b i) ⁅b j, b k⁆) +
        (F (b j) ⁅b i, b k⁆ - F ⁅b i, b k⁆ (b j)) +
          (F ⁅b i, b j⁆ (b k) - F (b k) ⁅b i, b j⁆) := by
      dsimp only [F]
      abel
    _ = 0 := hsum

private theorem reductionValue_disjoint_eq
    (b : Module.Basis I R L) (p m s : List I) (i j k l : I)
    (hji : j < i) (hlk : l < k)
    (hsmall : ∀ (q : List I) (a c : I) (t : List I), c < a →
      List.inversionWeight (q ++ a :: c :: t) <
          List.inversionWeight (p ++ i :: j :: (m ++ k :: l :: s)) →
        normalize b (q ++ a :: c :: t) = reductionValue b q a c t) :
    reductionValue b p i j (m ++ k :: l :: s) =
      reductionValue b (p ++ i :: j :: m) k l s := by
  have hleft : List.inversionWeight (p ++ j :: i :: (m ++ k :: l :: s)) <
      List.inversionWeight (p ++ i :: j :: (m ++ k :: l :: s)) :=
    List.inversionWeight_adjacent_swap_lt p i j (m ++ k :: l :: s) hji
  have hright : List.inversionWeight (p ++ i :: j :: (m ++ l :: k :: s)) <
      List.inversionWeight (p ++ i :: j :: (m ++ k :: l :: s)) := by
    simpa only [List.append_assoc, List.cons_append] using
      List.inversionWeight_adjacent_swap_lt (p ++ i :: j :: m) k l s hlk
  have hA : normalize b (p ++ j :: i :: (m ++ k :: l :: s)) =
      normalize b (p ++ j :: i :: (m ++ l :: k :: s)) +
        normalizationInsertion b (p ++ j :: i :: m) s ⁅b k, b l⁆ := by
    have h := hsmall (p ++ j :: i :: m) k l s hlk (by
      simpa only [List.append_assoc, List.cons_append] using hleft)
    simpa only [reductionValue, List.append_assoc, List.cons_append] using h
  have hB : normalize b (p ++ i :: j :: (m ++ l :: k :: s)) =
      normalize b (p ++ j :: i :: (m ++ l :: k :: s)) +
        normalizationInsertion b p (m ++ l :: k :: s) ⁅b i, b j⁆ := by
    simpa only [reductionValue] using hsmall p i j (m ++ l :: k :: s) hji hright
  let F := normalizationSeparatedPair b p m s
  have hA' : normalizationInsertion b p (m ++ k :: l :: s) =
      normalizationInsertion b p (m ++ l :: k :: s) + F.flip ⁅b k, b l⁆ := by
    apply b.ext
    intro a
    have ha : List.inversionWeight ((p ++ a :: m) ++ k :: l :: s) <
        List.inversionWeight (p ++ i :: j :: (m ++ k :: l :: s)) :=
      List.inversionWeight_lt_of_length_lt (by
        simp only [List.length_append, List.length_cons]
        omega)
    have h := hsmall (p ++ a :: m) k l s hlk ha
    simpa only [LinearMap.add_apply, LinearMap.flip_apply,
      normalizationInsertion_basis, F, normalizationSeparatedPair_basis_left,
      reductionValue, List.append_assoc, List.cons_append] using h
  have hB' : normalizationInsertion b (p ++ i :: j :: m) s =
      normalizationInsertion b (p ++ j :: i :: m) s + F ⁅b i, b j⁆ := by
    apply b.ext
    intro a
    have ha : List.inversionWeight (p ++ i :: j :: (m ++ a :: s)) <
        List.inversionWeight (p ++ i :: j :: (m ++ k :: l :: s)) :=
      List.inversionWeight_lt_of_length_lt (by
        simp only [List.length_append, List.length_cons]
        omega)
    have h := hsmall p i j (m ++ a :: s) hji ha
    simpa only [LinearMap.add_apply, normalizationInsertion_basis,
      F, normalizationSeparatedPair_basis_right, reductionValue,
      List.append_assoc, List.cons_append] using h
  have hAx := LinearMap.congr_fun hA' ⁅b i, b j⁆
  have hBy := LinearMap.congr_fun hB' ⁅b k, b l⁆
  simp only [LinearMap.add_apply, LinearMap.flip_apply] at hAx hBy
  rw [reductionValue, reductionValue]
  simp only [List.append_assoc, List.cons_append]
  rw [hA, hB, hAx, hBy]
  abel

private theorem reductionValue_eq_of_later_prefix
    (b : Module.Basis I R L) (p s r t : List I) (i j k l : I)
    (hrest : i :: j :: s = r ++ k :: l :: t) (hji : j < i) (hlk : l < k)
    (hsmall : ∀ (q : List I) (a c : I) (u : List I), c < a →
      List.inversionWeight (q ++ a :: c :: u) < List.inversionWeight (p ++ i :: j :: s) →
        normalize b (q ++ a :: c :: u) = reductionValue b q a c u) :
    reductionValue b p i j s = reductionValue b (p ++ r) k l t := by
  cases r with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at hrest
      rcases hrest with ⟨rfl, rfl, rfl⟩
      rw [List.append_nil]
  | cons a r =>
      cases r with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
          rcases hrest with ⟨rfl, rfl, rfl⟩
          exact reductionValue_overlap_eq b p t i j l hji hlk hsmall
      | cons c m =>
          simp only [List.cons_append, List.cons.injEq] at hrest
          rcases hrest with ⟨rfl, rfl, rfl⟩
          exact reductionValue_disjoint_eq b p m t i j k l hji hlk hsmall

private theorem reductionValue_same_word_eq
    (b : Module.Basis I R L) (p s q t : List I) (i j k l : I)
    (hword : p ++ i :: j :: s = q ++ k :: l :: t) (hji : j < i) (hlk : l < k)
    (hsmall : ∀ (r : List I) (a c : I) (u : List I), c < a →
      List.inversionWeight (r ++ a :: c :: u) < List.inversionWeight (p ++ i :: j :: s) →
        normalize b (r ++ a :: c :: u) = reductionValue b r a c u) :
    reductionValue b p i j s = reductionValue b q k l t := by
  rcases List.append_eq_append_iff.mp hword with ⟨r, hq, hr⟩ | ⟨r, hp, hr⟩
  · subst q
    exact reductionValue_eq_of_later_prefix b p s r t i j k l hr hji hlk hsmall
  · subst p
    have hsmall' : ∀ (r' : List I) (a c : I) (u : List I), c < a →
        List.inversionWeight (r' ++ a :: c :: u) < List.inversionWeight (q ++ k :: l :: t) →
          normalize b (r' ++ a :: c :: u) = reductionValue b r' a c u := by
      intro r' a c u hca hweight
      apply hsmall r' a c u hca
      simpa only [hword] using hweight
    exact (reductionValue_eq_of_later_prefix b q t r s k l i j hr hlk hji hsmall').symm

private theorem normalize_reduction_of_word (b : Module.Basis I R L) (xs : List I) :
    ∀ (p : List I) (i j : I) (s : List I), xs = p ++ i :: j :: s → j < i →
      normalize b xs = reductionValue b p i j s := by
  generalize hn : List.inversionWeight xs = n
  induction n using Nat.strong_induction_on generalizing xs with
  | ind n ih =>
      intro p i j s hword hji
      cases hsearch : List.adjacentInversion xs with
      | none =>
          have hsorted := List.pairwise_le_of_adjacentInversion_eq_none xs hsearch
          rw [hword] at hsorted
          have htail := (List.pairwise_append.mp hsorted).2.1
          have hij := (List.pairwise_cons.mp htail).1 j List.mem_cons_self
          exact (not_lt_of_ge hij hji).elim
      | some data =>
          rcases data with ⟨q, a, c, t⟩
          obtain ⟨hcanonical, hca⟩ := List.adjacentInversion_spec xs q a c t hsearch
          have hsmall : ∀ (r : List I) (x y : I) (u : List I), y < x →
              List.inversionWeight (r ++ x :: y :: u) <
                  List.inversionWeight (q ++ a :: c :: t) →
                normalize b (r ++ x :: y :: u) = reductionValue b r x y u := by
            intro r x y u hyx hweight
            apply ih (List.inversionWeight (r ++ x :: y :: u)) ?_
              (r ++ x :: y :: u) rfl r x y u rfl hyx
            rw [← hn, hcanonical]
            exact hweight
          exact (normalize_eq_reductionValue_of_search b hsearch).trans
            (reductionValue_same_word_eq b q t p s a c i j
              (hcanonical.symm.trans hword) hca hji hsmall)

/-- For a commutative ring R, an R-Lie algebra L with ordered
R-basis b, words p,s and indices j < i, the normal form satisfies
Norm(p ++ [i,j] ++ s) =
Norm(p ++ [j,i] ++ s) + Ins_(p,s)([b_i,b_j]).
The insertion is the basis expansion of the bracket in the same
prefix and suffix; the inverted pair may occur anywhere in the word. -/
theorem normalize_adjacent_inversion (b : Module.Basis I R L)
    (p : List I) (i j : I) (s : List I) (hji : j < i) :
    normalize b (p ++ i :: j :: s) =
      normalize b (p ++ j :: i :: s) +
        normalizationInsertion b p s ⁅b i, b j⁆ :=
  normalize_reduction_of_word b (p ++ i :: j :: s) p i j s rfl hji

/-- For a commutative ring R and an R-Lie algebra L with
ordered R-basis b, every p,s and i,j satisfy
Norm(p ++ [i,j] ++ s)−Norm(p ++ [j,i] ++ s)
= Ins_(p,s)([b_i,b_j]).
This includes i = j and both strict-order orientations. -/
theorem normalize_basis_relation (b : Module.Basis I R L)
    (p : List I) (i j : I) (s : List I) :
    normalize b (p ++ i :: j :: s) - normalize b (p ++ j :: i :: s) =
      normalizationInsertion b p s ⁅b i, b j⁆ := by
  rcases lt_trichotomy j i with hji | hji | hij
  · rw [normalize_adjacent_inversion b p i j s hji]
    abel
  · subst j
    simp only [sub_self, lie_self, map_zero]
  · rw [normalize_adjacent_inversion b p j i s hij,
      ← lie_skew (b i) (b j), map_neg]
    abel

/-- For a commutative ring R and an R-Lie algebra L with
ordered R-basis b, let Pair_(p,s)(x,y) be the bilinear basis
expansion of normal forms with x,y inserted adjacently.
For arbitrary x,y ∈ L it satisfies
Pair_(p,s)(x,y)−Pair_(p,s)(y,x) = Ins_(p,s)([x,y]),
where the insertion on the right is linear in the bracket vector. -/
theorem normalizationPair_commutator (b : Module.Basis I R L)
    (p s : List I) (x y : L) :
    normalizationPair b p s x y - normalizationPair b p s y x =
      normalizationInsertion b p s ⁅x, y⁆ :=
  pair_commutator_of_basis_identities b p s (normalize_basis_relation b p · · s) x y

end UniversalEnvelopingAlgebra.PBW
