/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Sylow
public import MathlibExt.GroupTheory.SigmaNilpotent
import Mathlib.GroupTheory.Transfer
import Mathlib.Order.Atoms.Finite

/-!
# σ-nilpotent supplements to maximal subgroups of Sylow subgroups (Kourovka Notebook Problem 19.88)

We prove that σ-nilpotent supplements to all maximal subgroups of Sylow subgroups force
the ambient finite group to be σ-nilpotent.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.88 (A. N.
Skiba). UnsolvedMath record UM-00701636 (`KOU-19.88`), dataset ulamai/UnsolvedMath v1.8.0.

A partition `σ` of the primes is a family `σ : I → Set ℕ` of nonempty, pairwise disjoint sets of
primes covering all primes; a positive integer (a finite group) is `σ`-primary when its prime
divisors (those of its order) lie in one block `σᵢ`. A finite group is `σ`-nilpotent when it is a
direct product of `σ`-primary groups (an internal direct product of finitely many normal `σ`-primary
subgroups). Maximal subgroups of `P` are the subgroups covered by `P` (`V ⋖ P`); `V T = G` means
every element is `v t`. Every partition `σ` is quantified. The `σ`-definitions are the shared ones
in `WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
The shared definitions are re-exported there from `MathlibExt.GroupTheory.SigmaSubnormal` and
`MathlibExt.GroupTheory.SigmaNilpotent`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SylowMaximalSigmaNilpotentSupplementKourovka19Problem88Wanted

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- **Kourovka Problem 19.88 (statement).** The statement that for every partition $\sigma$ of the
set of all primes and every finite group $G$: if for every prime $p$, every Sylow $p$-subgroup $P$
of $G$ and every maximal subgroup $V$ of $P$ there is a $\sigma$-nilpotent subgroup $T$ of $G$ with
$VT = G$, that is, every element of $G$ is a product $vt$ with $v \in V$ and $t \in T$, then $G$ is
$\sigma$-nilpotent. Here a partition of the primes is a family of nonempty, pairwise disjoint sets
of primes whose union is the set of all primes, and a group is $\sigma$-nilpotent when it is the
internal direct product of finitely many normal subgroups, each of whose order has all its prime
divisors in a single block of $\sigma$. -/
def sylowMaximalSigmaNilpotentSupplement : Prop :=
  ∀ (I : Type) (σ : I → Set ℕ), IsPrimePartition σ → ∀ (G : Type) [Group G] [Finite G],
    (∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (V : Subgroup G), V ⋖ (P : Subgroup G) →
      ∃ T : Subgroup G, IsSigmaNilpotent σ T ∧ ∀ g : G, ∃ v ∈ V, ∃ t ∈ T, v * t = g) →
    IsSigmaNilpotent σ G

open Subgroup MulAction

variable {I : Type} {σ : I → Set ℕ} {G : Type} [Group G] [Finite G]

private theorem eq_one_of_prime_pow {A : Type*} [Group A] [Finite A] {p n : ℕ} (hp : p.Prime)
    {a : A} (ha : a ^ p ^ n = 1) (h : ¬ p ∣ Nat.card A) : a = 1 :=
  orderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes ((hp.coprime_iff_not_dvd.mpr h).pow_left n)
    (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_natCard a)

-- In each direct factor, at least one of the two prime-power elements projects to one.
private theorem commute_in_product (hσ : IsPrimePartition σ) (hG : IsSigmaNilpotent σ G)
    {i : I} {p q m n : ℕ} (hp : p ∈ σ i) (hq : q.Prime) (hqi : q ∉ σ i)
    {x y : G} (hx : x ^ p ^ m = 1) (hy : y ^ q ^ n = 1) : Commute x y := by
  classical
  obtain ⟨t, H, hH, htop, hind⟩ := hG
  have hi : iSupIndep H := fun k ↦ disjoint_iff.mpr (hind k)
  have hc : Pairwise fun k l ↦ ∀ x y : G, x ∈ H k → y ∈ H l → Commute x y :=
    fun k l h ↦ commute_of_normal_of_disjoint _ _ (hH k).1 (hH l).1 (hi.pairwiseDisjoint h)
  let e := MulEquiv.ofBijective (noncommPiCoprod hc)
    ⟨injective_noncommPiCoprod_of_iSupIndep hi,
      MonoidHom.range_eq_top.mp ((noncommPiCoprod_range (hcomm := hc)).trans htop)⟩
  apply (commute_map_iff e.symm.injective).mp
  change e.symm x * e.symm y = e.symm y * e.symm x
  ext k : 1
  let f := (Pi.evalMonoidHom _ k).comp e.symm.toMonoidHom
  change f x * f y = f y * f x
  obtain ⟨j, hj⟩ := (hH k).2
  by_cases h : i = j
  · have he : f y = 1 := eq_one_of_prime_pow hq (by rw [← map_pow, hy, map_one])
      (fun hd ↦ hqi (h ▸ hj q hq hd))
    simp [he]
  · have hp' := (hσ.1 i).2 p hp
    have he : f x = 1 := eq_one_of_prime_pow hp' (by rw [← map_pow, hx, map_one])
      (fun hd ↦ Set.disjoint_left.mp (hσ.2.1 i j h) hp (hj p hp' hd))
    simp [he]

-- The cosets of T form a single V-orbit, so their number is a power of p.
-- A cyclic q-group fixes a coset, whose representative can be taken in V.
private theorem exists_conj_mem (V T : Subgroup G) {p q n : ℕ} (hV : IsPGroup p V)
    (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p)
    (hVT : ∀ g : G, ∃ v ∈ V, ∃ t ∈ T, v * t = g) {y : G} (hy : y ^ q ^ n = 1) :
    ∃ v ∈ V, (MulAut.conj v).symm y ∈ T := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  let base : G ⧸ T := QuotientGroup.mk (1 : G)
  have reps (z : G ⧸ T) : ∃ v : V, (QuotientGroup.mk v.val : G ⧸ T) = z := by
    obtain ⟨g, rfl⟩ := Quotient.exists_rep z
    obtain ⟨v, hv, t, ht, rfl⟩ := hVT g
    exact ⟨⟨v, hv⟩, (QuotientGroup.mk_mul_of_mem v ht).symm⟩
  have horb : orbit V base = Set.univ := by
    refine Set.eq_univ_of_forall fun z ↦ ?_
    obtain ⟨v, rfl⟩ := reps z
    exact ⟨v, congrArg QuotientGroup.mk (mul_one v.val)⟩
  obtain ⟨k, hk⟩ := hV.card_orbit base
  rw [horb, Nat.card_congr (Equiv.Set.univ _)] at hk
  have hc : IsPGroup q (zpowers y) := IsPGroup.of_card_dvd_pow
    (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hy)
  have hindex : ¬ q ∣ Nat.card (G ⧸ T) := by
    rw [hk]
    exact fun hd ↦ hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd))
  obtain ⟨z, hz⟩ := hc.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ T) hindex
  obtain ⟨v, rfl⟩ := reps z
  have he := mem_fixedPoints.mp hz (⟨y, mem_zpowers y⟩ : zpowers y)
  refine ⟨v, v.property, ?_⟩
  simpa [MulAut.conj_symm_apply, mul_assoc] using QuotientGroup.eq.mp he.symm

private theorem commute_of_supplements (hσ : IsPrimePartition σ)
    (hs : ∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (V : Subgroup G), V ⋖ (P : Subgroup G) →
      ∃ T : Subgroup G, IsSigmaNilpotent σ T ∧ ∀ g : G, ∃ v ∈ V, ∃ t ∈ T, v * t = g)
    {i : I} {p q m n : ℕ} (hp : p ∈ σ i) (hq : q.Prime) (hqi : q ∉ σ i)
    {x y : G} (hx : x ^ p ^ m = 1) (hy : y ^ q ^ n = 1) : Commute x y := by
  have hp' := (hσ.1 i).2 p hp
  have : Fact p.Prime := ⟨hp'⟩
  have hcyc : IsPGroup p (zpowers x) := IsPGroup.of_card_dvd_pow
    (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨P, hP⟩ := hcyc.exists_le_sylow
  suffices h : (P : Subgroup G) ≤ centralizer {y} from
    mem_centralizer_singleton_iff.mp (h (hP (mem_zpowers x)))
  -- A maximal subgroup containing the centralizing part of P would contain all of P.
  by_contra hn
  obtain ⟨V, hV, hmax⟩ := exists_le_covBy_of_lt (inf_lt_left.mpr hn)
  obtain ⟨T, hT, hVT⟩ := hs p hp' P V hmax
  obtain ⟨v, hv, hyv⟩ := exists_conj_mem V T (P.isPGroup.to_le hmax.le) hp' hq
    (fun he ↦ hqi (he ▸ hp)) hVT hy
  let e := MulAut.conj v
  have hvP := hmax.le hv
  have hPT (t : G) (ht : t ∈ T) (htP : t ∈ P) : t ∈ V := by
    obtain ⟨k, hk⟩ := P.isPGroup.exists_pow_pow_eq_one ⟨t, htP⟩
    have hcomm : Commute (⟨t, ht⟩ : T) ⟨e.symm y, hyv⟩ :=
      commute_in_product hσ hT hp hq hqi (Subtype.ext (congrArg (fun a : P ↦ (a : G)) hk))
        (Subtype.ext (by change (e.symm y) ^ q ^ n = 1; rw [← map_pow, hy, map_one]))
    have he : Commute (e t) y := by simpa using (hcomm.map T.subtype).map e
    have hvv : e t ∈ V := hV ⟨P.mul_mem (P.mul_mem hvP htP) (P.inv_mem hvP),
      mem_centralizer_singleton_iff.mpr he⟩
    have := V.mul_mem (V.mul_mem (V.inv_mem hv) hvv) hv
    simpa [e, MulAut.conj_apply, mul_assoc] using this
  apply hmax.lt.not_ge
  intro g hg
  obtain ⟨v', hv', t, ht, rfl⟩ := hVT g
  exact V.mul_mem hv' (hPT t ht ((P.mul_mem_cancel_left (hmax.le hv')).mp hg))

private def blockGenerators (s : Set ℕ) : Set G :=
  {x | ∃ p ∈ s, ∃ n : ℕ, x ^ p ^ n = 1}

omit [Finite G] in
private theorem normal_block (s : Set ℕ) : (closure (blockGenerators (G := G) s)).Normal := by
  constructor
  intro x hx g
  let e := MulAut.conj g
  have h : closure (blockGenerators s) ≤ (closure (blockGenerators s)).comap e.toMonoidHom := by
    apply (closure_le _).2
    rintro z ⟨p, hp, n, hn⟩
    exact subset_closure ⟨p, hp, n, by change (e z) ^ p ^ n = 1; rw [← map_pow, hn, map_one]⟩
  exact h hx

-- A Sylow subgroup for an outside prime centralizes all the generators. Burnside transfer
-- then gives a normal complement containing them, so the outside prime cannot divide the order.
private theorem prime_mem_block_of_dvd_card (hσ : IsPrimePartition σ) (i : I)
    (hc : ∀ {p q m n : ℕ}, p ∈ σ i → q.Prime → q ∉ σ i →
      ∀ {x y : G}, x ^ p ^ m = 1 → y ^ q ^ n = 1 → Commute x y) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card (closure (blockGenerators (G := G) (σ i))) → q ∈ σ i := by
  intro q hq hd
  by_contra hqi
  have : Fact q.Prime := ⟨hq⟩
  let H : Subgroup G := closure (blockGenerators (σ i))
  let Q : Sylow q H := default
  have hcent : normalizer (Q : Set H) ≤ centralizer (Q : Set H) := by
    intro z _
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨n, hn⟩ := Q.isPGroup.exists_pow_pow_eq_one ⟨y, hy⟩
    have hpow : (y : G) ^ q ^ n = 1 := congrArg (fun a : Q ↦ (a : G)) hn
    have h : H ≤ centralizer {(y : G)} := by
      apply (closure_le _).2
      rintro x ⟨p, hp, m, hm⟩
      exact mem_centralizer_singleton_iff.mpr (hc hp hq hqi hm hpow)
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (h z.property)).symm.eq
  let f := MonoidHom.transferSylow Q hcent
  have hker : H ≤ f.ker.map H.subtype := by
    apply (closure_le _).2
    rintro x hx
    obtain ⟨p, hp, n, hn⟩ := hx
    let a : H := ⟨x, subset_closure ⟨p, hp, n, hn⟩⟩
    refine ⟨a, ?_, rfl⟩
    obtain ⟨k, hk⟩ := Q.isPGroup.exists_pow_pow_eq_one (f a)
    have hf : (f a) ^ p ^ n = 1 := by
      rw [← map_pow, show a ^ p ^ n = 1 from Subtype.ext hn, map_one]
    have hne : p ≠ q := fun he ↦ hqi (he ▸ hp)
    exact orderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_pow_primes n k ((hσ.1 i).2 p hp) hq hne)
      (orderOf_dvd_of_pow_eq_one hf) (orderOf_dvd_of_pow_eq_one hk)
  have hk : f.ker = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b, hb, he⟩ := hker a.property
    exact H.subtype_injective he ▸ hb
  have hnot := MonoidHom.not_dvd_card_ker_transferSylow Q hcent
  change ¬ q ∣ Nat.card f.ker at hnot
  rw [hk, card_top] at hnot
  exact hnot hd

private theorem sigmaNilpotent_of_commute (hσ : IsPrimePartition σ)
    (hc : ∀ {i : I} {p q m n : ℕ}, p ∈ σ i → q.Prime → q ∉ σ i →
      ∀ {x y : G}, x ^ p ^ m = 1 → y ^ q ^ n = 1 → Commute x y) : IsSigmaNilpotent σ G := by
  classical
  -- Only blocks meeting the prime divisors of the group order are needed.
  let D := (Nat.card G).primeFactors
  have covers (p : D) := hσ.2.2 p.val (Nat.prime_of_mem_primeFactors p.property)
  let block (p : D) := (covers p).choose
  let J := Set.range block
  let e := (Fintype.equivFin J).symm
  let b (k : Fin (Fintype.card J)) : I := (e k).val
  have hb : Function.Injective b := Subtype.val_injective.comp e.injective
  let H (k : Fin (Fintype.card J)) : Subgroup G := closure (blockGenerators (σ (b k)))
  have hn (k) : (H k).Normal := normal_block _
  have hcard (k) := prime_mem_block_of_dvd_card (G := G) hσ (b k) (@hc (b k))
  have hcop : Pairwise fun k l ↦ (Nat.card (H k)).Coprime (Nat.card (H l)) := by
    intro k l hkl
    by_contra h
    obtain ⟨p, hp, hpk, hpl⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    exact Set.disjoint_left.mp (hσ.2.1 _ _ (hb.ne hkl)) (hcard k p hp hpk) (hcard l p hp hpl)
  have hcomm : Pairwise fun k l ↦ ∀ x y : G, x ∈ H k → y ∈ H l → Commute x y :=
    fun k l h ↦ commute_of_normal_of_disjoint _ _ (hn k) (hn l)
      (disjoint_of_coprime_natCard (hcop h))
  let (k : Fin (Fintype.card J)) : Fintype (H k) := Fintype.ofFinite _
  have hi := independent_of_coprime_order hcomm
    (by simpa only [← Nat.card_eq_fintype_card] using hcop)
  refine ⟨_, H, fun k ↦ ⟨hn k, b k, hcard k⟩, ?_, fun k ↦ disjoint_iff.mp (hi k)⟩
  -- The join contains a Sylow subgroup for every prime dividing its index.
  apply index_eq_one.mp
  by_contra h
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h
  have : Fact p.Prime := ⟨hp⟩
  let r : D := ⟨p, hp.mem_primeFactors (hd.trans (index_dvd_card _)) Nat.card_pos.ne'⟩
  let j : J := ⟨block r, r, rfl⟩
  let k := e.symm j
  have hpk : p ∈ σ (b k) := by simpa [b, k, j] using (covers r).choose_spec
  let P : Sylow p G := default
  have hP : (P : Subgroup G) ≤ H k := by
    intro x hx
    obtain ⟨n, hn⟩ := P.isPGroup.exists_pow_pow_eq_one ⟨x, hx⟩
    exact subset_closure ⟨p, hpk, n, congrArg (fun a : P ↦ (a : G)) hn⟩
  exact P.not_dvd_index (hd.trans (index_dvd_of_le (hP.trans (le_iSup H k))))

/--
**σ-nilpotent supplements to the maximal subgroups of Sylow subgroups (Kourovka 19.88).** Let
$\sigma$ be a partition of the set of all primes and let $G$ be a finite group. If for every prime
$p$, every Sylow $p$-subgroup $P$ of $G$ and every maximal subgroup $V$ of $P$ there is a
$\sigma$-nilpotent subgroup $T$ of $G$ with $VT = G$, that is, every element of $G$ is a product
$vt$ with $v \in V$ and $t \in T$, then $G$ is $\sigma$-nilpotent. Here a partition of the primes is
a family of nonempty, pairwise disjoint sets of primes whose union is the set of all primes, and a
group is $\sigma$-nilpotent when it is the internal direct product of finitely many normal
subgroups, each of whose order has all its prime divisors in a single block of $\sigma$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.88 (A. N.
Skiba); resolution: A.-M. Liu, W. Guo, I. N. Safonova and A. N. Skiba, G-covering subgroup systems
for some classes of σ-soluble groups, J. Algebra 585 (2021), 280-293; another solution using CFSG by
S. F. Kamornikov and V. N. Tyutyanov, Trudy Inst. Mat. Mekh. UrO RAN 27 (2021), no. 1, 98-102,
abstract: a set of subgroups of G containing a supplement to each maximal subgroup of every Sylow
subgroup of G is a G-covering subgroup system for the classes of σ-soluble and of σ-nilpotent
groups, which answers 19.87 and 19.88; Kourovka Archive, Problem 19.88: Yes, it is true,
https://doi.org/10.1016/j.jalgebra.2021.06.010.
-/
theorem sylowMaximalSigmaNilpotentSupplement_holds :
    sylowMaximalSigmaNilpotentSupplement := by
  intro I σ hσ G _ _ hs
  apply sigmaNilpotent_of_commute hσ
  intro i p q m n hp hq hqi x y hx hy
  exact commute_of_supplements hσ hs hp hq hqi hx hy

end MathlibExt.GroupTheory.SylowMaximalSigmaNilpotentSupplementKourovka19Problem88Wanted
