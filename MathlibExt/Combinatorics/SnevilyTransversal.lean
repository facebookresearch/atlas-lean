/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.FieldTheory.Finite.Basic

/-!
# Snevily's conjecture on Latin transversals

We prove that equal-sized subsets of an odd-order abelian group admit a bijection with
distinct sums. The unique-multiset argument of Harcos, Károlyi and Kós
(https://arxiv.org/abs/1004.0253) is combined with symmetrization in the group algebra
of tuples over the field of two elements.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SnevilyTransversalWanted

/-- **Snevily's conjecture.** The statement that for every finite abelian group $G$ of odd order,
written additively, and all subsets $A, B \subseteq G$ with $|A| = |B|$, there is a bijection
$f \colon A \to B$ such that the sums $a + f(a)$, for $a \in A$, are pairwise distinct.

Equivalently, $A$ and $B$ can be enumerated as $a_1, \dots, a_k$ and $b_1, \dots, b_k$ so that
the sums $a_i + b_i$ are pairwise distinct: given such enumerations, send $a_i$ to $b_i$;
conversely, enumerate $A$ and transport the enumeration along $f$.

Source: OPG-655. -/
def conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G],
    Odd (Fintype.card G) →
      ∀ A B : Finset G, A.card = B.card →
        ∃ f : ↥A → ↥B, Function.Bijective f ∧
          ∀ a₁ a₂ : ↥A,
            (a₁ : G) + (f a₁ : G) = (a₂ : G) + (f a₂ : G) → a₁ = a₂

open Finset Function Equiv

variable {I G : Type}

section Matching

variable [Fintype I]

/-- A maximum-weight assignment cannot gain weight by exchanging two columns. -/
private lemma swap_bound (w : I → I → ℕ) (p : Perm I)
    (hp : ∀ q : Perm I, ∑ i, w i (q i) ≤ ∑ i, w i (p i)) {i k : I} (hik : i ≠ k) :
    w i (p k) ≤ w i (p i) + w k (p k) := by
  classical
  let t : Finset I := {i, k}
  have hsplit (f : I → ℕ) : ∑ x, f x = ∑ x ∈ univ \ t, f x + (f i + f k) := by
    rw [← sum_sdiff (s₁ := t) (subset_univ _)]; simp [t, hik]
  have h := hp (p * swap i k)
  rw [hsplit, hsplit (fun x => w x (p x))] at h
  have he : ∑ x ∈ univ \ t, w x ((p * swap i k) x) =
      ∑ x ∈ univ \ t, w x (p x) := by
    apply sum_congr rfl
    intro x hx
    simp only [t, mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hx
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2]
  rw [he] at h
  simp only [Perm.mul_apply, swap_apply_left, swap_apply_right] at h
  omega

/-- Rank the symbols and assign weight `3 ^ rank` to each edge. A maximum-weight matching
must use the highest-ranked edge in any rectangle of rows and columns it matches internally. -/
private lemma forced_edge (r : I → I → ℕ) (hr : ∀ i, Injective (r i))
    (hc : ∀ j, Injective (fun i => r i j)) (p : Perm I)
    (hp : ∀ q : Perm I, ∑ i, 3 ^ r i (q i) ≤ ∑ i, 3 ^ r i (p i))
    (i j : I) (hrow : r i (p i) ≤ r i j) (hcol : r (p.symm j) j ≤ r i j) :
    p i = j := by
  by_contra hn
  have hi : i ≠ p.symm j := fun h => hn (h ▸ p.apply_symm_apply j)
  have h₁ := lt_of_le_of_ne hrow ((hr i).ne hn)
  have h₂ := lt_of_le_of_ne hcol ((hc j).ne hi.symm)
  have bound := swap_bound (fun x y => 3 ^ r x y) p hp hi
  simp only [apply_symm_apply] at bound
  have pow_bound {a b : ℕ} (h : a < b) : 3 * 3 ^ a ≤ 3 ^ b := by
    simpa [pow_succ, Nat.mul_comm] using
      (Nat.pow_le_pow_right (by decide : 0 < 3) (show a + 1 ≤ b from h))
  have := pow_bound h₁
  have := pow_bound h₂
  have : 0 < 3 ^ r i j := Nat.pow_pos (by decide)
  omega

/-- The maximum weight is attained by exactly one permutation. If two maximizers disagree,
take a highest-ranked edge between the rows and columns on which they disagree.
Both maximizers must contain that edge. -/
private lemma unique_weight (r : I → I → ℕ) (hr : ∀ i, Injective (r i))
    (hc : ∀ j, Injective (fun i => r i j)) :
    ∃ p : Perm I, ∀ q : Perm I, (∑ i, 3 ^ r i (q i) : ℕ) = ∑ i, 3 ^ r i (p i) → q = p := by
  classical
  let score (p : Perm I) : ℕ := ∑ i, 3 ^ r i (p i)
  obtain ⟨p, -, hp⟩ := univ.exists_max_image score univ_nonempty
  have hmax (s : Perm I) : score s ≤ score p := hp s (mem_univ _)
  refine ⟨p, fun q (he : score q = score p) => ?_⟩
  by_contra hqp
  obtain ⟨k, hk⟩ : ∃ k, p k ≠ q k := by
    by_contra! hall
    exact hqp (Equiv.ext hall).symm
  let t := univ.filter fun z : I × I => p z.1 ≠ q z.1 ∧ p.symm z.2 ≠ q.symm z.2
  have ht (i j : I) : (i, j) ∈ t ↔ p i ≠ q i ∧ p.symm j ≠ q.symm j := by simp [t]
  have images (u v : Perm I) (i : I) (hi : u i ≠ v i) :
      u.symm (u i) ≠ v.symm (u i) ∧ u.symm (v i) ≠ v.symm (v i) := by
    simp only [symm_apply_apply, ne_eq, eq_symm_apply, symm_apply_eq]
    exact ⟨Ne.symm hi, Ne.symm hi⟩
  have col := images p q
  have row := images p.symm q.symm
  obtain ⟨⟨i, j⟩, hij, hm⟩ := t.exists_max_image (fun z => r z.1 z.2)
    ⟨(k, p k), (ht ..).2 ⟨hk, (col k hk).1⟩⟩
  obtain ⟨hi, hj⟩ := (ht ..).1 hij
  have h₁ := forced_edge r hr hc p hmax i j
    (hm (_, _) ((ht ..).2 ⟨hi, (col i hi).1⟩)) (hm (_, _) ((ht ..).2 ⟨(row j hj).1, hj⟩))
  have h₂ := forced_edge r hr hc q (fun s => (hmax s).trans_eq he.symm) i j
    (hm (_, _) ((ht ..).2 ⟨hi, (col i hi).2⟩)) (hm (_, _) ((ht ..).2 ⟨(row j hj).2, hj⟩))
  exact hi (h₁.trans h₂.symm)

end Matching

variable [AddCommGroup G]

private abbrev TupleAlgebra (I G : Type) [AddCommGroup G] := AddMonoidAlgebra (ZMod 2) (I → G)

private noncomputable def permute (s : Perm I) : TupleAlgebra I G →+* TupleAlgebra I G :=
  AddMonoidAlgebra.mapDomainRingHom _ ⟨⟨fun x => x ∘ s, rfl⟩, fun _ _ => rfl⟩

private lemma permute_single (s : Perm I) (x : I → G) (c : ZMod 2) :
    permute s (AddMonoidAlgebra.single x c) = AddMonoidAlgebra.single (x ∘ s) c :=
  AddMonoidAlgebra.mapDomain_single

private lemma permute_permute (s t : Perm I) (v : TupleAlgebra I G) :
    permute s (permute t v) = permute (t * s) v := by
  induction v using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single => simp only [permute_single]; rfl

private lemma permute_one (v : TupleAlgebra I G) : permute (1 : Perm I) v = v := by
  induction v using AddMonoidAlgebra.induction_linear with
  | zero => exact map_zero _
  | add x y hx hy => simp [hx, hy]
  | single => rw [permute_single]; rfl

variable [Fintype I] [DecidableEq I]

private noncomputable def symmetrize (v : TupleAlgebra I G) : TupleAlgebra I G :=
  ∑ s : Perm I, permute s v

private lemma permute_symmetrize (s : Perm I) (v : TupleAlgebra I G) :
    permute s (symmetrize v) = symmetrize v := by
  simp only [symmetrize, map_sum, permute_permute]
  exact Equiv.sum_comp (Equiv.mulRight s) fun t => permute t v

private lemma symmetrize_mul (x v : TupleAlgebra I G) (hv : ∀ s : Perm I, permute s v = v) :
    symmetrize (x * v) = symmetrize x * v := by
  simp [symmetrize, map_mul, hv, sum_mul]

/-- A tuple with a repeated entry has zero orbit sum in characteristic two. -/
private lemma symmetrize_collision {x : I → G} (hx : ¬ Injective x) :
    symmetrize (AddMonoidAlgebra.single x 1) = 0 := by
  classical
  obtain ⟨i, j, he, hn⟩ : ∃ i j, x i = x j ∧ i ≠ j := by simpa [Injective] using hx
  let t := swap i j
  have ht : x ∘ t = x := by
    funext k
    by_cases h : k = i <;> by_cases h' : k = j <;> simp_all [t, swap_apply_def]
  have ht₁ : t ≠ 1 := fun h => hn (by simpa [t] using (Equiv.congr_fun h i).symm)
  have ht₂ : t * t = 1 := Equiv.swap_mul_self i j
  simp only [symmetrize, permute_single]
  apply sum_ninvolution (fun s : Perm I => t * s)
  · intro s
    have h : x ∘ (t * s : Perm I) = x ∘ s := congrArg (fun y : I → G => y ∘ s) ht
    rw [h]
    exact ZModModule.add_self _
  · intro s _ eq
    exact ht₁ (mul_right_cancel (eq.trans (one_mul s).symm))
  · simp
  · intro s
    rw [← mul_assoc, ht₂, one_mul]

/-- Raise the orbit sum to a power of two congruent to one modulo the group order.
Frobenius acts on each basis tuple by scalar multiplication by that same power. -/
private lemma symmetrize_pow [Fintype G] (hodd : Odd (Fintype.card G)) (x : I → G) :
    ∃ m : ℕ, symmetrize (AddMonoidAlgebra.single x 1) ^ (m + 2) =
      symmetrize (AddMonoidAlgebra.single x 1) := by
  let : CharP (TupleAlgebra I G) 2 :=
    charP_of_injective_ringHom
      (AddMonoidAlgebra.singleZeroRingHom (R := ZMod 2) (M := I → G)).injective 2
  let n := (Fintype.card G).totient
  have hn : 0 < n := Nat.totient_pos.mpr Fintype.card_pos
  have htwo : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ n from hn)
  have hmod := Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hodd)
  have htuple (y : I → G) : (2 ^ n) • y = y := by
    funext i
    exact (nsmul_eq_nsmul_iff_modEq.mpr (hmod.of_dvd addOrderOf_dvd_card)).trans (one_nsmul _)
  refine ⟨2 ^ n - 2, ?_⟩
  rw [Nat.sub_add_cancel htwo]
  simp only [symmetrize, permute_single, sum_pow_char_pow, AddMonoidAlgebra.single_pow,
    one_pow, htuple]

/-- Collect the coefficients of all tuples of a given total weight. -/
private noncomputable def weightCoeff (w : G → ℕ) (k : ℕ) : TupleAlgebra I G →+ ZMod 2 :=
  (Finsupp.applyAddHom k).comp ((Finsupp.mapDomain.addMonoidHom
    (fun x : I → G => ∑ i, w (x i))).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

omit [DecidableEq I] in
private lemma weightCoeff_single (w : G → ℕ) (k : ℕ) (x : I → G) (c : ZMod 2) :
    weightCoeff w k (AddMonoidAlgebra.single x c) = if ∑ i, w (x i) = k then c else 0 := by
  simp [weightCoeff, Finsupp.single_apply]

omit [DecidableEq I] in
private lemma weightCoeff_permute (s : Perm I) (w : G → ℕ) (k : ℕ) (v : TupleAlgebra I G) :
    weightCoeff w k (permute s v) = weightCoeff w k v := by
  induction v using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single x c =>
    simp only [permute_single, weightCoeff_single, comp_apply]
    rw [Equiv.sum_comp s (fun i => w (x i))]

/-- Symmetrization can be transferred between the two factors under an invariant functional. -/
private lemma transfer (L : TupleAlgebra I G →+ ZMod 2)
    (hL : ∀ (s : Perm I) v, L (permute s v) = L v) (x y : TupleAlgebra I G) :
    L (x * symmetrize y) = L (symmetrize x * y) := by
  simp only [symmetrize, mul_sum, sum_mul, map_sum]
  calc
    _ = ∑ s : Perm I, L (permute s⁻¹ x * y) := by
      apply sum_congr rfl
      intro s _
      rw [← hL s⁻¹ (x * permute s y), map_mul, permute_permute, mul_inv_cancel, permute_one]
    _ = _ := Equiv.sum_comp (Equiv.inv _) fun s : Perm I => L (permute s x * y)

/-- If every pairing has a collision, the product of the two orbit sums vanishes. -/
private lemma orbit_product_zero (a b : I → G)
    (h : ∀ s : Perm I, ¬ Injective (a + b ∘ s)) :
    symmetrize (AddMonoidAlgebra.single a 1) * symmetrize (AddMonoidAlgebra.single b 1) = 0 := by
  rw [← symmetrize_mul _ _ (fun s => permute_symmetrize s _)]
  simp only [symmetrize, mul_sum, permute_single, AddMonoidAlgebra.single_mul_single, mul_one,
    map_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro s _
  simpa only [symmetrize, permute_single] using symmetrize_collision (h s)

/-- On an odd-order group a vanishing orbit product forces every invariant coefficient of
the partially symmetrized product to vanish as well. -/
private lemma weightCoeff_zero [Fintype G] (hodd : Odd (Fintype.card G)) (a b : I → G)
    (h : ∀ s : Perm I, ¬ Injective (a + b ∘ s)) (w : G → ℕ) (k : ℕ) :
    weightCoeff w k
      (AddMonoidAlgebra.single a 1 * symmetrize (AddMonoidAlgebra.single b 1)) = 0 := by
  let x : TupleAlgebra I G := AddMonoidAlgebra.single a 1
  let y : TupleAlgebra I G := AddMonoidAlgebra.single b 1
  let v := symmetrize y
  obtain ⟨m, hm : v ^ (m + 2) = v⟩ := symmetrize_pow hodd b
  have hv (s : Perm I) : permute s (v ^ (m + 1)) = v ^ (m + 1) := by
    rw [map_pow, permute_symmetrize]
  have hz : symmetrize x * v = 0 := orbit_product_zero a b h
  change weightCoeff w k (x * v) = 0
  calc
    _ = weightCoeff w k ((x * v ^ (m + 1)) * symmetrize y) := by
      rw [mul_assoc, ← pow_succ, hm]
    _ = weightCoeff w k (symmetrize (x * v ^ (m + 1)) * y) :=
      transfer _ (fun s => weightCoeff_permute s w k) _ _
    _ = 0 := by rw [symmetrize_mul _ _ hv, pow_succ', ← mul_assoc, hz, zero_mul, zero_mul, map_zero]

/--
**Snevily's conjecture is true.** Let $G$ be a finite abelian group of odd order, written
additively, and let $A, B \subseteq G$ be subsets with $|A| = |B|$. Then there is a bijection
$f \colon A \to B$ such that the sums $a + f(a)$, for $a \in A$, are pairwise distinct.

Source:
Boris Arsovski, A proof of Snevily's conjecture, Israel J. Math. 182 (2011), 505-508. Moved from
`OpenConjectures/Combinatorics/SnevilyTransversal`.
-/
public theorem conjecture_holds : conjecture := by
  classical
  intro G _ _ hodd A B hAB
  let e : A ≃ B := Fintype.equivOfCardEq (by simpa using hAB)
  let a : A → G := Subtype.val
  let b : A → G := fun i => e i
  suffices ∃ p : Perm A, Injective (a + b ∘ p) by
    obtain ⟨p, hp⟩ := this
    exact ⟨p.trans e, (p.trans e).bijective, fun _ _ he => hp he⟩
  by_contra! h
  let rank (g : G) : ℕ := (Fintype.equivFin G g).val
  have hrank : Injective rank := Fin.val_injective.comp (Fintype.equivFin G).injective
  have ha : Injective a := Subtype.val_injective
  have hb : Injective b := Subtype.val_injective.comp e.injective
  obtain ⟨p, hp⟩ := unique_weight (fun i j => rank (a i + b j))
    (fun i => hrank.comp ((add_right_injective (a i)).comp hb))
    (fun j => hrank.comp ((add_left_injective (b j)).comp ha))
  let w (g : G) := 3 ^ rank g
  let score (q : Perm A) : ℕ := ∑ i, w (a i + b (q i))
  have hscore (q : Perm A) : score q = score p ↔ q = p := ⟨hp q, fun hq => hq ▸ rfl⟩
  have hz := weightCoeff_zero hodd a b h w (score p)
  simp only [symmetrize, mul_sum, permute_single, AddMonoidAlgebra.single_mul_single, mul_one,
    map_sum, weightCoeff_single] at hz
  change (∑ q : Perm A, if score q = score p then (1 : ZMod 2) else 0) = 0 at hz
  simp [hscore] at hz

end MathlibExt.Combinatorics.SnevilyTransversalWanted
