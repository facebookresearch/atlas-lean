/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.Action.End
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.Tactic.LinearCombination

/-!
# Group-ring powers in fields with a finite automorphism group (Kourovka Notebook Problem 11.79)

Every subfield containing all the prescribed powers contains infinitely many fixed elements.

Kourovka Notebook, Archive of Solved Problems, Problem 11.79 (K. N. Ponomarëv): let `G` be a finite
group of automorphisms of an infinite field `F` of characteristic `p`; integral powers and the
action of `G` define an action of `ℤG` on `Fˣ`. Does every subfield of `F` that contains the images
of all elements of `F` under a fixed element of `ℤG \ pℤG` contain infinitely many `G`-invariant
elements?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.79 (K. N.
Ponomarëv). UnsolvedMath record UM-00700771 (`KOU-11.79`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a finite subgroup of `RingAut F` and `ξ ∈ ℤG` a finitely supported function `G → ℤ`, acting
by `x ^ ξ = ∏_g (g x) ^ (ξ g)` on nonzero `x`; `ξ ∉ pℤG` means some coefficient is not divisible by
`p`. The characteristic is a prime `p`: in characteristic 0 every subfield contains `ℚ`, which is
infinite and fixed by `G`, so the statement would be trivial.

## Proof

Write `E` for the fixed field. Along a line `1 + b * u` with `u ∈ E`, the prescribed power is a
rational function of `u`. Independence of the automorphisms gives a choice of `b` for which its
derivative at zero is nonzero. Comparing the linear coefficients of its values under two field
embeddings that agree on `K` shows that the embeddings agree on `E`. Applying this to the residue
fields of the tensor square over `K` puts a Frobenius power of each element of `E` in `K ∩ E`.
If this intersection were finite, its Frobenius would be bijective, forcing it to contain all
of the infinite field `E`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FieldAutomorphismGroupRingKourovka11Problem79Wanted

/-- **Group-ring powers and invariant elements (Kourovka 11.79).** The proposition that the
following holds for every prime $p$, every infinite field $F$ of characteristic $p$, every finite
group $G$ of ring automorphisms of $F$, and every element $\xi = \sum_{g \in G} \xi_g \, g$ of the
group ring $\mathbb{Z}G$ with $\xi \notin p\mathbb{Z}G$, that is, with some integer coefficient
$\xi_g$ not divisible by $p$. For nonzero $x \in F$ put $x^\xi = \prod_{g \in G} g(x)^{\xi_g}$.
If a subfield $K$ of $F$ contains $x^\xi$ for every nonzero $x \in F$, then $K$ contains
infinitely many elements $y$ with $g(y) = y$ for all $g \in G$. -/
def subfieldContainsInfinitelyManyInvariants : Prop :=
  ∀ (p : ℕ) (F : Type) [Field F] [CharP F p], p.Prime → Infinite F →
    ∀ G : Subgroup (RingAut F), (G : Set (RingAut F)).Finite →
    ∀ ξ : G →₀ ℤ, (¬ ∀ g : G, (p : ℤ) ∣ ξ g) →
    ∀ K : Subfield F, (∀ x : F, x ≠ 0 → (ξ.prod fun g n => ((g : RingAut F) x) ^ n) ∈ K) →
      {y : F | y ∈ K ∧ ∀ g ∈ G, g y = y}.Infinite

open Polynomial
open scoped BigOperators

variable {E L : Type*} [Field E] [Infinite E] [Field L]

-- A positive product of powers of two field embeddings cannot be trivial on the units.
private lemma no_positive_relation (f h : E →+* L) {a b : ℕ} (ha : 0 < a)
    (hr : ∀ x : E, x ≠ 0 → f x ^ a * h x ^ b = 1) : False := by
  by_cases hb : b = 0
  · subst b
    have he := (X ^ a : L[X]).eq_of_infinite_eval_eq 1 (by
      apply ((Set.infinite_range_of_injective f.injective).sdiff (Set.finite_singleton 0)).mono
      rintro _ ⟨⟨x, rfl⟩, hx⟩
      have hx' : x ≠ 0 := by rintro rfl; simp at hx
      simpa using hr x hx')
    simpa [ha.ne'] using congrArg (eval 0) he
  -- Apply the relation at both x and 1 + xᵇ. Clearing denominators gives a polynomial
  -- identity whose two sides have different constant terms.
  let P : L[X] := (1 + X ^ b) ^ a * (1 + X ^ a) ^ b
  let Q : L[X] := X ^ (a * b)
  have hn : (1 + X ^ b : L[X]) ≠ 0 := by
    intro e
    simpa [hb] using congrArg (eval 0) e
  have he : P = Q := P.eq_of_infinite_eval_eq Q (by
    apply (((Set.infinite_range_of_injective f.injective).sdiff (Set.finite_singleton 0)).sdiff
      (finite_setOfPred_isRoot hn)).mono
    rintro _ ⟨⟨⟨x, rfl⟩, hx⟩, hy⟩
    have hx' : f x ≠ 0 := hx
    have hx0 : x ≠ 0 := fun e => hx' (e ▸ map_zero f)
    have hy' : 1 + x ^ b ≠ 0 := by
      intro e
      apply hy
      simpa [IsRoot] using congrArg f e
    have h1 := hr x hx0
    have h2 := hr (1 + x ^ b) hy'
    simp only [map_add, map_one, map_pow] at h2
    have h3 : f x ^ a * (1 + h x ^ b) = 1 + f x ^ a := by linear_combination h1
    simp only [Set.mem_ofPred_eq, P, Q, eval_mul, eval_pow, eval_add, eval_one, eval_X]
    rw [← h3, mul_pow, ← pow_mul]
    linear_combination (f x ^ (a * b)) * h2)
  simpa [P, Q, ha.ne', hb] using congrArg (eval 0) he

private def character (f h : E →+* L) (i j : ℕ) : E →* L :=
  f.toMonoidHom ^ i * h.toMonoidHom ^ j

private lemma left_collision (f h : E →+* L) {i j : ℕ} (hne : (i, j) ≠ (1, 0))
    (he : character f h i j = f.toMonoidHom) :
    ∃ n : ℕ, ∀ x : E, f x = h x ^ n := by
  cases i with
  | zero => exact ⟨j, fun x => by simpa [character] using (DFunLike.congr_fun he x).symm⟩
  | succ i =>
    have hr (x : E) (hx : x ≠ 0) : f x ^ i * h x ^ j = 1 := by
      have e := DFunLike.congr_fun he x
      simp [character, pow_succ] at e
      apply mul_left_cancel₀ (show f x ≠ 0 by simpa using hx)
      linear_combination e
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := by rintro rfl; exact hne rfl
      exact (no_positive_relation h f (b := 0) (Nat.pos_of_ne_zero hj)
        (fun x hx => by simpa using hr x hx)).elim
    · exact (no_positive_relation f h (Nat.pos_of_ne_zero hi) hr).elim

-- In a vanishing character sum a nonzero coefficient must meet another copy of its character.
private lemma exists_collision {I M : Type*} [Monoid M] (s : Finset I)
    (v : I → M →* L) (c : I → L) (k : I) (hk : k ∈ s) (hc : c k ≠ 0)
    (hs : ∀ x : M, ∑ i ∈ s, c i * v i x = 0) : ∃ i ∈ s, i ≠ k ∧ v i = v k := by
  classical
  by_contra! hn
  let l := ∑ i ∈ s, Finsupp.single (v i) (c i)
  have hl : Finsupp.linearCombination L (fun f : M →* L => (f : M → L)) l = 0 := by
    ext x
    simpa [l, Finsupp.linearCombination_single, Finset.sum_apply] using hs x
  have hz := (linearIndependent_iff.mp (linearIndependent_monoidHom M L)) l hl
  apply hc
  have h := DFunLike.congr_fun hz (v k)
  simp only [l, Finsupp.finsetSum_apply, Finsupp.zero_apply] at h
  rwa [Finset.sum_eq_single k (fun i hi hik => Finsupp.single_eq_of_ne (hn i hi hik).symm)
    (by simp [hk]), Finsupp.single_eq_same] at h

-- Compare the two embeddings on the linear coefficient of a rational function at zero.
private lemma embedding_is_power {F : Type*} [Field F] (A B : F →+* L) (e : E →+* F)
    (P Q : F[X]) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (hd : P.coeff 1 ≠ Q.coeff 1)
    (he : ∀ t : E, A (P.eval (e t)) * B (Q.eval (e t)) =
      A (Q.eval (e t)) * B (P.eval (e t))) :
    ∃ n : ℕ, ∀ x : E, A (e x) = B (e x) ^ n := by
  classical
  let N := max P.natDegree Q.natDegree + 2
  let s := Finset.range N
  let f := A.comp e
  let h := B.comp e
  let v (ij : ℕ × ℕ) := character f h ij.1 ij.2
  let c (ij : ℕ × ℕ) :=
    A (P.coeff ij.1) * B (Q.coeff ij.2) - A (Q.coeff ij.1) * B (P.coeff ij.2)
  have hPN : P.natDegree < N := by dsimp [N]; omega
  have hQN : Q.natDegree < N := by dsimp [N]; omega
  obtain ⟨⟨i, j⟩, _, hne, hv⟩ := exists_collision (s ×ˢ s) v c (1, 0)
    (by simp [s, N]) (by simpa [c, hP, hQ, sub_ne_zero] using A.injective.ne hd) (by
      intro x
      have hx := sub_eq_zero.mpr (he x)
      simp only [eval_eq_sum_range' hPN, eval_eq_sum_range' hQN, map_sum, map_pow, map_mul,
        Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib] at hx
      rw [Finset.sum_comm] at hx
      have happ (i j : ℕ) : v (i, j) x = A (e x) ^ i * B (e x) ^ j := rfl
      simpa only [s, c, Finset.sum_product, happ, sub_mul,
        mul_mul_mul_comm (A _) (B _)] using hx)
  apply left_collision f h hne
  simpa [v, character] using hv

private lemma embeddings_agree {F : Type*} [Field F] (A B : F →+* L) (e : E →+* F)
    (P Q : F[X]) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (hd : P.coeff 1 ≠ Q.coeff 1)
    (he : ∀ t : E, A (P.eval (e t)) * B (Q.eval (e t)) =
      A (Q.eval (e t)) * B (P.eval (e t))) (t : E) : A (e t) = B (e t) := by
  obtain ⟨n, hn⟩ := embedding_is_power A B e P Q hP hQ hd he
  obtain ⟨m, hm⟩ := embedding_is_power B A e P Q hP hQ hd
    (fun x => by simpa only [mul_comm] using (he x).symm)
  have hpoly : (X : L[X]) = X ^ (m * n) := X.eq_of_infinite_eval_eq _ (by
    apply (Set.infinite_range_of_injective (A.injective.comp e.injective)).mono
    rintro _ ⟨x, rfl⟩
    simpa [pow_mul] using (hn x).trans (congrArg (· ^ n) (hm x)))
  have hdeg := congrArg natDegree hpoly
  simp only [natDegree_X, natDegree_X_pow] at hdeg
  have h1 : n = 1 := Nat.eq_one_of_dvd_one (hdeg ▸ Nat.dvd_mul_left n m)
  simpa [h1] using hn t

open scoped TensorProduct

-- Test the two inclusions in the tensor square modulo each prime. Their difference is
-- nilpotent, so a Frobenius power lies in the equalizer, which is the base field.
private lemma exists_pow_mem {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (K : Subfield F) (e : E →+* F) (P Q : F[X])
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) (hd : P.coeff 1 ≠ Q.coeff 1)
    (he : ∀ t : E, P.eval (e t) / Q.eval (e t) ∈ K) (t : E) :
    ∃ n : ℕ, (e t) ^ p ^ n ∈ K := by
  let T := F ⊗[K] F
  let A : F →ₐ[K] T := Algebra.TensorProduct.includeLeft
  let B : F →ₐ[K] T := Algebra.TensorProduct.includeRight
  have hz : IsNilpotent (A (e t) - B (e t)) := by
    apply nilpotent_iff_mem_prime.mpr
    intro J hJ
    let π := algebraMap T J.ResidueField
    have agree (x : F) (hx : x ∈ K) : A x = B x := (A.commutes ⟨x, hx⟩).trans
      (B.commutes ⟨x, hx⟩).symm
    have hc := embeddings_agree (π.comp A.toRingHom) (π.comp B.toRingHom) e P Q hP hQ hd
      (fun u => by
        let a := P.eval (e u)
        let b := Q.eval (e u)
        change π (A a) * π (B b) = π (A b) * π (B a)
        by_cases hb : b = 0
        · simp [hb]
        have eq := congrArg π (agree (a / b) (he u))
        change (π.comp A.toRingHom) (a / b) = (π.comp B.toRingHom) (a / b) at eq
        rw [map_div₀, map_div₀, div_eq_div_iff] at eq
        · exact eq.trans (mul_comm ..)
        · exact (map_ne_zero (π.comp A.toRingHom)).mpr hb
        · exact (map_ne_zero (π.comp B.toRingHom)).mpr hb) t
    apply Ideal.algebraMap_residueField_eq_zero.mp
    rw [map_sub, sub_eq_zero]
    exact hc
  obtain ⟨n, hn⟩ := hz
  have hle : n ≤ p ^ n := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have heq := pow_eq_zero_of_le hle hn
  have : CharP T p := charP_of_injective_ringHom A.injective p
  change iterateFrobenius T p n (A (e t) - B (e t)) = 0 at heq
  rw [map_sub, sub_eq_zero] at heq
  change A (e t) ^ p ^ n = B (e t) ^ p ^ n at heq
  have hs : Algebra.TensorProduct.includeLeftSubRight K F ((e t) ^ p ^ n) = 0 := by
    change A ((e t) ^ p ^ n) - B ((e t) ^ p ^ n) = 0
    simpa only [map_pow, sub_eq_zero] using heq
  obtain ⟨k, hk⟩ := (Algebra.IsEffective.of_faithfullyFlat K F _).mp hs
  exact ⟨n, hk ▸ k.property⟩

private lemma first_coefficient {F I : Type*} [Field F] (s : Finset I)
    (b : I → F) (k : I → ℕ) :
    (∏ i ∈ s, (1 + C (b i) * X) ^ k i).coeff 1 = ∑ i ∈ s, (k i : F) * b i := by
  classical
  let P := ∏ i ∈ s, (1 + C (b i) * X) ^ k i
  have h : P.coeff 1 = P.derivative.eval 0 := by
    simp [← coeff_zero_eq_eval_zero, coeff_derivative]
  rw [h]
  simp [P, derivative_prod_finset, derivative_pow, eval_prod, eval_finsetSum, derivative_mul]

private lemma exists_direction {F : Type*} [Field F] (p : ℕ) [CharP F p]
    (G : Subgroup (RingAut F)) (ξ : G →₀ ℤ) (hξ : ¬ ∀ g : G, (p : ℤ) ∣ ξ g) :
    ∃ b : F, ∑ g ∈ ξ.support, (ξ g : F) * (g : RingAut F) b ≠ 0 := by
  classical
  by_contra! h
  let v (g : G) : F →* F := (g : RingAut F).toRingHom.toMonoidHom
  have hv : Function.Injective v := fun g h eq => Subtype.ext <| RingEquiv.ext
    (fun x => DFunLike.congr_fun eq x)
  have hzero : ∑ g ∈ ξ.support, (ξ g : F) • (v g : F → F) = 0 := by
    ext b
    simpa [Finset.sum_apply, v] using h b
  apply hξ
  intro g
  apply (CharP.intCast_eq_zero_iff F p _).mp
  by_cases hg : g ∈ ξ.support
  · exact linearIndependent_iff'.mp ((linearIndependent_monoidHom F F).comp v hv)
      ξ.support (fun g => (ξ g : F)) hzero g hg
  · simp [Finsupp.notMem_support_iff.mp hg]

private lemma zpow_parts {F : Type*} [Field F] (x : F) (n : ℤ) :
    x ^ n.toNat / x ^ (-n).toNat = x ^ n := by
  cases n <;> simp [zpow_negSucc]

private lemma coeff_parts {F : Type*} [Field F] (n : ℤ) :
    (n.toNat : F) - ((-n).toNat : F) = (n : F) := by
  cases n <;> simp

private lemma fixed_pow_mem {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (G : Subgroup (RingAut F)) (ξ : G →₀ ℤ) (hξ : ¬ ∀ g : G, (p : ℤ) ∣ ξ g)
    (K : Subfield F)
    (hK : ∀ x : F, x ≠ 0 → (ξ.prod fun g n => ((g : RingAut F) x) ^ n) ∈ K)
    [Infinite (FixedPoints.subfield G F)] (t : FixedPoints.subfield G F) :
    ∃ n : ℕ, (t : F) ^ p ^ n ∈ K := by
  classical
  -- On the line 1 + b u with u fixed by G, the group-ring power is P(u) / Q(u).
  -- Independence of the automorphisms gives a direction b with nonzero linear term.
  obtain ⟨b, hb⟩ := exists_direction p G ξ hξ
  let c (g : G) := (g : RingAut F) b
  let poly (k : G → ℕ) := ∏ g ∈ ξ.support, (1 + C (c g) * X) ^ k g
  let P := poly fun g => (ξ g).toNat
  let Q := poly fun g => (-ξ g).toNat
  apply exists_pow_mem p K (FixedPoints.subfield G F).subtype P Q
  · simp [P, poly, coeff_zero_eq_eval_zero, eval_prod]
  · simp [Q, poly, coeff_zero_eq_eval_zero, eval_prod]
  · apply sub_ne_zero.mp
    simpa only [P, Q, poly, first_coefficient, ← Finset.sum_sub_distrib, ← sub_mul,
      coeff_parts] using hb
  · intro u
    let x := 1 + b * (u : F)
    have hu (g : G) : (g : RingAut F) x = 1 + c g * (u : F) := by
      change _ = 1 + (g : RingAut F) b * (u : F)
      rw [show (g : RingAut F) x = 1 + (g : RingAut F) b * (g : RingAut F) u by simp [x]]
      rw [show (g : RingAut F) u = u from u.property g]
    have he : P.eval (u : F) / Q.eval (u : F) = ξ.prod fun g n => ((g : RingAut F) x) ^ n := by
      simp only [P, Q, poly, eval_prod, eval_pow, eval_add, eval_one, eval_mul, eval_C, eval_X,
        ← Finset.prod_div_distrib, zpow_parts, Finsupp.prod, hu]
    rw [show (FixedPoints.subfield G F).subtype u = (u : F) from rfl, he]
    by_cases hx : x = 0
    · apply K.prod_mem
      intro g _
      simpa [hx] using K.zpow_mem K.zero_mem (ξ g)
    · exact hK x hx

private lemma infinite_intersection {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (K E : Subfield F) [Infinite E] (hp : ∀ x : E, ∃ n : ℕ, (x : F) ^ p ^ n ∈ K) :
    ((K ⊓ E : Subfield F) : Set F).Infinite := by
  classical
  intro h
  let H := K ⊓ E
  have : Finite H := h.to_subtype
  have hmem (x : E) : (x : F) ∈ H := by
    obtain ⟨n, hn⟩ := hp x
    let y : H := ⟨(x : F) ^ p ^ n, hn, E.pow_mem x.property _⟩
    obtain ⟨z, hz⟩ := Finite.surjective_of_injective (iterateFrobenius_inj H p n) y
    have eq : (z : F) = x := iterateFrobenius_inj F p n (congrArg Subtype.val hz)
    exact eq ▸ z.property
  apply not_finite_iff_infinite.mpr (inferInstance : Infinite E)
  exact Finite.of_injective (fun x : E => (⟨x.val, hmem x⟩ : H))
    (fun _ _ eq => Subtype.ext (congrArg (fun z : H => (z : F)) eq))

/-- **Subfields containing all group-ring powers have infinitely many invariants.** Let $p$ be a
prime, $F$ an infinite field of characteristic $p$, $G$ a finite group of ring automorphisms of
$F$, and $\xi = \sum_{g \in G} \xi_g \, g$ an element of the group ring $\mathbb{Z}G$ with
$\xi \notin p\mathbb{Z}G$, that is, with some integer coefficient $\xi_g$ not divisible by $p$.
For nonzero $x \in F$ put $x^\xi = \prod_{g \in G} g(x)^{\xi_g}$. If a subfield $K$ of $F$
contains $x^\xi$ for every nonzero $x \in F$, then $K$ contains infinitely many elements $y$ with
$g(y) = y$ for all $g \in G$. This is the positive answer to Kourovka Notebook Problem 11.79,
given by K. N. Ponomarëv (1992).

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 11.79 (K. N. Ponomarëv); resolution: K. N. Ponomarëv,
Siberian Math. J. 33 (1992), 1094-1099, Kourovka Archive, Problem 11.79: "Yes",
https://arxiv.org/abs/1401.0300v49.
-/
theorem subfieldContainsInfinitelyManyInvariants_holds :
    subfieldContainsInfinitelyManyInvariants := by
  intro p F _ _ hp hF G hG ξ hξ K hK
  have : Fact p.Prime := ⟨hp⟩
  have : Finite G := hG.to_subtype
  let E := FixedPoints.subfield G F
  have : Infinite E := by
    apply not_finite_iff_infinite.mp
    intro h
    exact (not_finite_iff_infinite.mpr hF) (Module.finite_of_finite E)
  apply (infinite_intersection p K E (fixed_pow_mem p G ξ hξ K hK)).mono
  intro x hx
  exact ⟨hx.1, fun g hg => hx.2 (⟨g, hg⟩ : G)⟩

end MathlibExt.GroupTheory.FieldAutomorphismGroupRingKourovka11Problem79Wanted
