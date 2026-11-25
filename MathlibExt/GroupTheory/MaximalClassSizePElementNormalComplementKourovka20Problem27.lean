/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Maximal class-size p-parts and normal p-complements

The semidirect product of a cyclic group of order eight by the symmetric group on four letters,
acting by the sign, refutes the implication in Kourovka Notebook Problem 20.27. A transposition
lifts to an involution of class size 24, every class size divides 24, and a normal 2-complement
would have order three.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalClassSizePElementNormalComplementKourovka20Problem27Wanted

/-- **Groups with a normal p-complement.** A group $G$ has a normal $p$-complement when it has a
normal subgroup $N$ and a Sylow $p$-subgroup $P$ that are complements of each other: every element
of $G$ can be written uniquely as $nq$ with $n \in N$ and $q \in P$. -/
def HasNormalPComplement (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (N : Subgroup G) (P : Sylow p G), N.Normal ∧ N.IsComplement' P

/-- **Gorshkov's problem on maximal p-parts of class sizes.** For a prime $p$, the $p$-part of a
positive integer $m$ is the largest power of $p$ dividing $m$. This is the statement that for
every finite group $G$, every prime $p$ and every $p$-element $g$ of $G$ (that is, $g^{p^k} = 1$
for some natural number $k$), if for every $x \in G$ the $p$-part of the size of the conjugacy
class of $x$ is at most the $p$-part of the size of the conjugacy class of $g$, then $G$ has a
normal $p$-complement.

This is Kourovka Notebook Problem 20.27 (I. B. Gorshkov). -/
def maximalClassSizePElementGivesNormalComplement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ g : G, (∃ k : ℕ, g ^ p ^ k = 1) →
    (∀ x : G, ordProj[p] (Nat.card (ConjClasses.mk x).carrier) ≤
      ordProj[p] (Nat.card (ConjClasses.mk g).carrier)) →
    HasNormalPComplement p G

private abbrev S := Equiv.Perm (Fin 4)
private abbrev C := Multiplicative (ZMod 8)
private def act : S →* MulAut C :=
  (MulAutMultiplicative (ZMod 8)).symm.toMonoidHom.comp
    ((DistribMulAction.toAddAut ℤˣ (ZMod 8)).comp Equiv.Perm.sign)
private abbrev G := C ⋊[act] S

-- Enumerate permutations directly in the finite centralizer calculation.
private local instance permFintype : Fintype S := fintypePerm
private local instance groupFinite : Finite G :=
  Finite.of_equiv (C × S) SemidirectProduct.equivProd.symm

private lemma card_G : Nat.card G = 192 := by
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
    Nat.card_eq_fintype_card]
  decide

private lemma act_apply (s : S) (a : C) : (act s a).toAdd = (s.sign : ℤ) • a.toAdd := rfl

-- An element over an even permutation commutes with the kernel of the projection to S₄.
private lemma classSize_dvd_of_even (x : G) (hx : x.right.sign = 1) :
    Nat.card (ConjClasses.mk x).carrier ∣ 24 := by
  let f : G →* S := SemidirectProduct.rightHom
  have hsub : f.ker ≤ Subgroup.centralizer {x} := by
    rintro ⟨a, s⟩ hs
    change s = 1 at hs
    subst s
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply SemidirectProduct.ext
    · change a * act 1 x.left = x.left * act x.right a
      have ha : act x.right a = a := by
        apply Multiplicative.toAdd.injective
        simp [act_apply, hx]
      simp [ha, mul_comm]
    · simp
  have hi : f.ker.index = 24 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective,
      Subgroup.card_top, Nat.card_eq_fintype_card]
    decide
  change (conjugatesOf x).ncard ∣ 24
  simpa only [hi, Subgroup.index_centralizer_eq_ncard] using Subgroup.index_dvd_of_le hsub

-- An odd permutation in S₄ has four commuting permutations. Each has two lifts
-- that centralize x, as seen by solving the commutation equation in Z/8.
private lemma odd_centralizer (x : G) (hx : x.right.sign ≠ 1) :
    Nat.card (Subgroup.centralizer {x}) = 8 := by
  let a := x.left.toAdd
  let s := x.right
  let commutingPerms := {r : S // r * s = s * r}
  let solutions (r : S) := {b : ZMod 8 // b + (r.sign : ℤ) • a = a - b}
  have hs : x.right.sign = -1 := (Int.units_eq_one_or s.sign).resolve_left hx
  have comm (y : G) : y ∈ Subgroup.centralizer {x} ↔
      y.left.toAdd + (y.right.sign : ℤ) • a = a - y.left.toAdd ∧ y.right * s = s * y.right := by
    rw [Subgroup.mem_centralizer_singleton_iff, commute_iff_eq, SemidirectProduct.ext_iff]
    apply and_congr_left
    intro _
    rw [← Multiplicative.toAdd.injective.eq_iff]
    simp [SemidirectProduct.mul_left, act_apply, a, hs, sub_eq_add_neg]
  let e : Subgroup.centralizer {x} ≃ (Σ r : commutingPerms, solutions r.1) :=
    { toFun := fun ⟨y, hy⟩ ↦
        ⟨⟨y.right, ((comm y).mp hy).2⟩, ⟨y.left.toAdd, ((comm y).mp hy).1⟩⟩
      invFun := fun ⟨r, b⟩ ↦
        ⟨⟨Multiplicative.ofAdd b.1, r.1⟩, (comm _).mpr ⟨b.2, r.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have two (r : S) : Fintype.card (solutions r) = 2 := by
    change Fintype.card {b : ZMod 8 // _} = 2
    rw [Fintype.card_subtype]
    rcases Int.units_eq_one_or r.sign with h | h <;> rw [h] <;>
      generalize a = z <;> revert z <;> decide
  have four : Fintype.card commutingPerms = 4 := by
    change Fintype.card {r : S // _} = 4
    rw [Fintype.card_subtype]
    exact (show ∀ z : S, z.sign ≠ 1 → (Finset.univ.filter fun r : S ↦ r * z = z * r).card = 4 by
      decide) s hx
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp [two, four]

private lemma classSize_of_odd (x : G) (hx : x.right.sign ≠ 1) :
    Nat.card (ConjClasses.mk x).carrier = 24 := by
  change (conjugatesOf x).ncard = 24
  rw [← Subgroup.index_centralizer_eq_ncard, Subgroup.index_eq_card_div, card_G,
    odd_centralizer x hx]

private lemma noNormalComplement : ¬ HasNormalPComplement 2 G := by
  rintro ⟨N, P, hN, hc⟩
  have hp : Nat.card P = 64 := by
    rw [P.card_eq_multiplicity, card_G]
    change 2 ^ (2 ^ 6 * 3).factorization 2 = 64
    rw [Nat.factorization_mul_apply_of_coprime (by decide),
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
    decide
  have hi : N.index = 64 := hc.symm.index_eq_card.trans hp
  have hn : Nat.card N = 3 := by
    have h := N.card_mul_index
    rw [hi, card_G] at h
    omega
  -- Both 3-cycles must belong to N, yet their product is a nonidentity involution.
  let emb : S →* G := SemidirectProduct.inr
  let u : S := Equiv.swap 0 1 * Equiv.swap 1 2
  let v : S := Equiv.swap 0 1 * Equiv.swap 1 3
  have member (s : S) (hs : s ^ 3 = 1) : emb s ∈ N := by
    have h64 : s ^ 64 = s := by
      change s ^ (3 * 21 + 1) = s
      rw [pow_succ, pow_mul, hs, one_pow, one_mul]
    simpa only [hi, ← map_pow, h64] using N.pow_index_mem (emb s)
  have hu := member u (by decide)
  have hv := member v (by decide)
  let w : N := ⟨emb u * emb v, N.mul_mem hu hv⟩
  have hw : w ^ 3 = 1 := hn ▸ pow_card_eq_one' (x := w)
  have h : emb ((u * v) ^ 3) = emb 1 := by
    rw [map_pow, map_mul, map_one]
    exact congrArg Subtype.val hw
  exact absurd (SemidirectProduct.inr_injective h) (by decide)

/--
**A maximal p-part of a class size does not force a normal p-complement.** For a prime $p$, the
$p$-part of a positive integer $m$ is the largest power of $p$ dividing $m$. There exist a finite
group $G$, a prime $p$ and a $p$-element $g$ of $G$ (that is, $g^{p^k} = 1$ for some natural
number $k$) such that for every $x \in G$ the $p$-part of the size of the conjugacy class of $x$
is at most the $p$-part of the size of the conjugacy class of $g$, but $G$ has no normal
$p$-complement.

Sambale's counterexample is the group $\mathrm{SL}(2, 3) \rtimes Q_8$ of order $192$ (number $945$
in the GAP library of small groups) with $p = 2$. In it an element of order $4$ has class size
$24$, whose $2$-part $8$ is the largest $2$-part of a class size, while the eight elements of
order $3$ form one conjugacy class, so there is no normal subgroup of order $3$, that is, no
normal $2$-complement.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.27 (I. B. Gorshkov); resolution: B.
Sambale, letter of 16 February 2022, recorded in the Kourovka Notebook (21st issue), Problem 20.27:
"No, not necessarily, a counterexample is given by SmallGroup(192,945)",
https://arxiv.org/abs/1401.0300v49.
-/
theorem maximalClassSizePElementGivesNormalComplement_refuted :
    ¬ maximalClassSizePElementGivesNormalComplement := by
  intro h
  let t : S := Equiv.swap 0 1
  let g : G := SemidirectProduct.inr t
  have hg : g ^ 2 = 1 := by
    change SemidirectProduct.inr t ^ 2 = (1 : G)
    rw [← map_pow, show t ^ 2 = 1 by decide, map_one]
  have hclass := classSize_of_odd g (by decide : t.sign ≠ 1)
  apply noNormalComplement (h G 2 Nat.prime_two g ⟨1, hg⟩ ?_)
  intro x
  rw [hclass]
  by_cases hx : x.right.sign = 1
  · exact Nat.le_of_dvd (Nat.ordProj_pos _ _)
      (Nat.ordProj_dvd_ordProj_of_dvd (by decide) (classSize_dvd_of_even x hx) 2)
  · rw [classSize_of_odd x hx]

end MathlibExt.GroupTheory.MaximalClassSizePElementNormalComplementKourovka20Problem27Wanted
