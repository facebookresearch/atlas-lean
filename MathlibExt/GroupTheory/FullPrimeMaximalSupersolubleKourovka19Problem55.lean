/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.GroupTheory.Solvable
public import MathlibExt.GroupTheory.FittingHeight

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.RepresentationTheory.Maschke

/-!
# Unbounded Fitting height under Monakhov's condition

We prove the Fitting-height part of Alexander Moretó's Theorem B for Kourovka Notebook
Problem 19.55(b), UnsolvedMath record UM-00701603 (`KOU-19.55`). The examples are built
by successive semidirect products with faithful irreducible elementary abelian kernels
at fresh primes. Every proper subgroup of each example misses a prime divisor of the
group order. Maschke's theorem supplies the modules from the regular representation.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

namespace MathlibExt.GroupTheory.FullPrimeMaximalSupersolubleKourovka19Problem55Wanted

@[expose] public section

/-- **Supersoluble group (generator form).** A group $G$ is supersoluble when there are a natural
number $n$ and elements $g_0, \dots, g_{n-1}$ of $G$ that generate $G$ such that, for every
$i \le n$, the subgroup $G_i = \langle g_j : j < i \rangle$ is normal in $G$.

Then $1 = G_0 \le \dots \le G_n = G$ is a normal series with cyclic factors
$G_{i+1} / G_i = \langle G_i, g_i \rangle / G_i$. -/
def IsSupersoluble (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), (∀ i : ℕ, i ≤ n → (Subgroup.closure (g '' {j | j.val < i})).Normal) ∧
    Subgroup.closure (Set.range g) = ⊤

/-- **Monakhov's condition.** A group $G$ satisfies Monakhov's condition when every maximal
subgroup $M$ of $G$ with $\pi(M) = \pi(G)$ is supersoluble, where $\pi(X)$ is the set of prime
factors of the order of $X$ if $X$ is finite, and is empty if $X$ is infinite. -/
def MaximalFullPrimeSupersoluble (G : Type*) [Group G] : Prop :=
  ∀ M : Subgroup G, IsCoatom M → (Nat.card M).primeFactors = (Nat.card G).primeFactors →
    IsSupersoluble M

/-- **Kourovka 19.55(b) (Monakhov): unbounded Fitting height.** The proposition that for every
natural number $h$ there is a finite soluble group $G$ whose Fitting height is greater than $h$ and
in which every maximal subgroup $M$ with $\pi(M) = \pi(G)$ is supersoluble, where $\pi(X)$ is the
set of primes dividing the order of $X$. -/
def fittingHeightUnbounded : Prop :=
  ∀ h : ℕ, ∃ (G : Type) (_ : Group G) (_ : Finite G), Group.IsSolvable G ∧
    MaximalFullPrimeSupersoluble G ∧ ¬ FittingHeightLE G h

end

open scoped MonoidAlgebra
open SemidirectProduct

noncomputable section

private def algebraAction (p : ℕ) (G V : Type) [Group G] [AddCommGroup V]
    [Module (ZMod p)[G] V] : G →* MulAut (Multiplicative V) :=
  letI : DistribMulAction G V := DistribMulAction.compHom V (MonoidAlgebra.of (ZMod p) G)
  (MulAutMultiplicative V).symm.toMonoidHom.comp (DistribMulAction.toAddAut G V)

-- A simple summand of the regular module moves the common nonidentity element.
-- Any nontrivial kernel would contain that element.
private lemma exists_faithful_simple {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp : ¬ p ∣ Nat.card G) (a : G) (ha : a ≠ 1)
    (ha_mem : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → a ∈ N) :
    ∃ S : Submodule (ZMod p)[G] (ZMod p)[G],
      IsSimpleModule (ZMod p)[G] S ∧ Function.Injective (algebraAction p G S) := by
  let R := (ZMod p)[G]
  let : NeZero (Nat.card G : ZMod p) := ⟨by simpa [ZMod.natCast_eq_zero_iff] using hp⟩
  have hsum := IsSemisimpleModule.sSup_simples_eq_top R R
  have hnot : MonoidAlgebra.of (ZMod p) G a - 1 ∉ (⊤ : Submodule R R).annihilator := by
    intro h
    have hzero := Submodule.mem_annihilator.mp h (1 : R) Submodule.mem_top
    apply ha
    apply MonoidAlgebra.of_injective (R := ZMod p) (M := G)
    rw [map_one]
    exact sub_eq_zero.mp (by simpa [R] using hzero)
  rw [← hsum, sSup_eq_iSup', Submodule.annihilator_iSup, Ideal.mem_iInf] at hnot
  push Not at hnot
  obtain ⟨⟨S, hS⟩, hmove⟩ := hnot
  refine ⟨S, hS, (algebraAction p G S).ker_eq_bot_iff.mp (by_contra fun hker ↦ hmove ?_)⟩
  have hmem := ha_mem _ (algebraAction p G S).normal_ker hker
  refine Submodule.mem_annihilator.mpr fun v hv ↦ ?_
  have hact := congrArg (fun f : MulAut (Multiplicative S) ↦
    (f (Multiplicative.ofAdd ⟨v, hv⟩)).toAdd.val) ((algebraAction p G S).mem_ker.mp hmem)
  change MonoidAlgebra.of (ZMod p) G a • v = v at hact
  rw [sub_smul, one_smul, hact, sub_self]

section Extension

variable {p : ℕ} {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod p)[G] V]

local notation "E" => Multiplicative V ⋊[algebraAction p G V] G
local notation "π" => (rightHom : E →* G)
local notation "ι" => (inl : Multiplicative V →* E)
local notation "K" => MonoidHom.ker π

private lemma mul_inl (x : E) (v : Multiplicative V) :
    x * ι v = ι (algebraAction p G V x.right v) * x := by
  ext <;> simp [mul_comm]

private lemma right_eq_one_of_commutes
    (hfaith : Function.Injective (algebraAction p G V)) {x : E}
    (h : ∀ v : Multiplicative V, Commute x (ι v)) : π x = 1 := by
  apply hfaith
  rw [map_one]
  ext v
  have hv := congrArg SemidirectProduct.left ((mul_inl x v).symm.trans (h v).eq)
  simpa using hv

private lemma inl_pow_eq_one (v : Multiplicative V) : (ι v) ^ p = 1 := by
  rw [← map_pow, ← map_one ι, inl_inj]
  change p • v.toAdd = 0
  have hz : (p : (ZMod p)[G]) = 0 := by
    rw [← map_natCast (algebraMap (ZMod p) (ZMod p)[G]), ZMod.natCast_self, map_zero]
  rw [← Nat.cast_smul_eq_nsmul (ZMod p)[G], hz, zero_smul]

private lemma ker_pow_eq_one {x : E} (hx : x ∈ K) : x ^ p = 1 := by
  rw [← range_inl_eq_ker_rightHom] at hx
  obtain ⟨v, rfl⟩ := hx
  exact inl_pow_eq_one v

-- The intersection with the kernel corresponds to an invariant submodule.
private lemma ker_le_of_stable {T : Subgroup E} [Fact (Nat.Prime p)]
    [IsSimpleModule (ZMod p)[G] V]
    (hstable : ∀ g : G, ∃ x : E, x.right = g ∧ x ∈ Subgroup.normalizer T)
    (hne : T ⊓ K ≠ ⊥) : K ≤ T := by
  let : Module (ZMod p) V := Module.compHom V (algebraMap (ZMod p) (ZMod p)[G])
  have : IsScalarTower (ZMod p) (ZMod p)[G] V := IsScalarTower.of_compHom _ _ _
  let S : Submodule (ZMod p)[G] V :=
    { carrier := {v | ι (Multiplicative.ofAdd v) ∈ T}
      zero_mem' := T.one_mem
      add_mem' := fun {v w} hv hw ↦ by
        change ι (Multiplicative.ofAdd v * Multiplicative.ofAdd w) ∈ T
        rw [map_mul]
        exact T.mul_mem hv hw
      smul_mem' := fun r v hv ↦ by
        change ι (Multiplicative.ofAdd (r • v)) ∈ T
        induction r using MonoidAlgebra.induction_on with
        | of g =>
          obtain ⟨x, hx, hxT⟩ := hstable g
          have hconj := (Subgroup.mem_normalizer_iff.mp hxT _).mp hv
          rw [mul_inl x, mul_inv_cancel_right, hx] at hconj
          exact hconj
        | add r s hr hs =>
          rw [add_smul]
          change ι (Multiplicative.ofAdd (r • v) * Multiplicative.ofAdd (s • v)) ∈ T
          rw [map_mul]
          exact T.mul_mem hr hs
        | smul c r hr =>
          rw [smul_assoc, ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
          change ι ((Multiplicative.ofAdd (r • v)) ^ c.val) ∈ T
          rw [map_pow]
          exact T.pow_mem hr _ }
  have htop : S = ⊤ := by
    rcases eq_bot_or_eq_top S with hs | hs
    · exfalso
      apply hne
      refine le_bot_iff.mp fun x hx ↦ ?_
      have hxK := hx.2
      rw [← range_inl_eq_ker_rightHom] at hxK
      obtain ⟨v, rfl⟩ := hxK
      have hv : v.toAdd ∈ S := hx.1
      rw [hs, Submodule.mem_bot] at hv
      have h1 : v = 1 := hv
      simp [h1]
    · exact hs
  rw [← range_inl_eq_ker_rightHom]
  rintro _ ⟨v, rfl⟩
  change v.toAdd ∈ S
  rw [htop]
  exact Submodule.mem_top

private lemma ker_le_of_normal {T : Subgroup E} [Fact (Nat.Prime p)]
    [IsSimpleModule (ZMod p)[G] V] [T.Normal]
    (hfaith : Function.Injective (algebraAction p G V)) (hne : T ≠ ⊥) : K ≤ T := by
  apply ker_le_of_stable (fun g ↦ ⟨inr g, rfl, by simp [Subgroup.normalizer_eq_top]⟩)
  intro hbot
  have hcomm : ⁅T, K⁆ = ⊥ :=
    le_bot_iff.mp (hbot ▸ Subgroup.commutator_le_inf T K)
  have hTK : T ≤ K := fun x hx ↦ right_eq_one_of_commutes hfaith fun v ↦ by
    have hv := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
    exact (Subgroup.mem_centralizer_iff.mp hv _ (by simp)).symm
  exact hne (by simpa [inf_eq_left.mpr hTK] using hbot)

-- Raising an element to the fresh prime gives an element of order coprime to that prime.
-- Inside a nilpotent subgroup, it must then centralize the elementary abelian kernel.
private lemma nilpotent_le_ker [Finite G] [Fact (Nat.Prime p)]
    [IsSimpleModule (ZMod p)[G] V] {N : Subgroup E} [N.Normal] [Group.IsNilpotent N]
    (hp : ¬ p ∣ Nat.card G) (hfaith : Function.Injective (algebraAction p G V)) :
    N ≤ K := by
  by_cases hN : N = ⊥
  · rw [hN]
    exact bot_le
  have hK : K ≤ N := ker_le_of_normal hfaith hN
  have hpG : p.Coprime (Nat.card G) := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hxG : x ^ Nat.card G ∈ K := MonoidHom.mem_ker.mpr (by rw [map_pow, pow_card_eq_one'])
  let y : N := ⟨x, hx⟩
  have hy : orderOf (y ^ p) ∣ Nat.card G := by
    rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, Nat.mul_comm, pow_mul]
    apply Subtype.ext
    exact ker_pow_eq_one hxG
  have hc (v : Multiplicative V) : Commute (x ^ p) (ι v) := by
    let w : N := ⟨ι v, hK (by simp)⟩
    have hw : orderOf w ∣ p := orderOf_dvd_iff_pow_eq_one.mpr
      (by exact Subtype.ext (inl_pow_eq_one v))
    exact (Group.IsNilpotent.commute_of_orderOf_coprime
      (x := y ^ p) (y := w) (hpG.symm.of_dvd hy hw)).map N.subtype
  have hpow : (π x) ^ p = 1 := by
    rw [← map_pow]
    exact right_eq_one_of_commutes hfaith hc
  apply orderOf_eq_one_iff.mp
  rw [← Nat.dvd_one, ← hpG.gcd_eq_one, Nat.dvd_gcd_iff]
  exact ⟨orderOf_dvd_iff_pow_eq_one.mpr hpow, orderOf_dvd_natCard _⟩

-- The first term after the identity maps to the identity, so the projected series is shorter.
private lemma fittingHeight_of_extension [Finite G] [Fact (Nat.Prime p)]
    [IsSimpleModule (ZMod p)[G] V] (hp : ¬ p ∣ Nat.card G)
    (hfaith : Function.Injective (algebraAction p G V)) {h : ℕ}
    (hs : FittingHeightLE E (h + 1)) : FittingHeightLE G h := by
  obtain ⟨s, hs0, hsend, hs⟩ := hs
  have hN : (s 1).Normal := by
    by_cases hh : h = 0
    · subst h
      rw [hsend]
      infer_instance
    · exact (hs 1 (by omega)).1
  obtain ⟨c, hc⟩ := (hs 0 (Nat.zero_lt_succ _)).2.2
  have hnil : Group.IsNilpotent (s 1) :=
    (Subgroup.isNilpotent_iff_lowerCentralSeries (s 1)).mpr ⟨c, le_bot_iff.mp (hs0 ▸ hc)⟩
  refine ⟨fun i ↦ (s (i + 1)).map π, ?_, ?_, ?_⟩
  · exact (Subgroup.map_eq_bot_iff _).mpr (nilpotent_le_ker hp hfaith)
  · change (s (h + 1)).map π = ⊤
    rw [hsend, Subgroup.map_top_of_surjective _ rightHom_surjective]
  · intro i hi
    obtain ⟨hn, hle, d, hd⟩ := hs (i + 1) (by omega)
    exact ⟨hn.map _ rightHom_surjective, Subgroup.map_mono hle, d,
      by rw [← Subgroup.map_lowerCentralSeries]; exact Subgroup.map_mono hd⟩

private def FullPrimeForcesTop (G : Type) [Group G] : Prop :=
  ∀ T : Subgroup G, (Nat.card T).primeFactors = (Nat.card G).primeFactors → T = ⊤

-- Elements of prime order detect which primes must occur in the projection and in its kernel.
private lemma extension_fullPrimeForcesTop [Finite G] [Finite V] [Fact (Nat.Prime p)]
    [IsSimpleModule (ZMod p)[G] V] (hp : ¬ p ∣ Nat.card G)
    (hG : FullPrimeForcesTop G) : FullPrimeForcesTop E := by
  have hpprime : p.Prime := Fact.out
  have : Finite E := Finite.of_equiv _ equivProd.symm
  intro T hT
  have hpE : p ∣ Nat.card E := by
    have : Nontrivial V := IsSimpleModule.nontrivial (ZMod p)[G] V
    obtain ⟨v, hv⟩ := exists_ne (1 : Multiplicative V)
    have hvOrder : orderOf (ι v) = p :=
      orderOf_eq_prime (inl_pow_eq_one v) (fun h ↦ hv (inl_injective (h.trans (map_one ι).symm)))
    simpa only [hvOrder] using orderOf_dvd_natCard (ι v)
  have hpT : p ∣ Nat.card T := Nat.dvd_of_mem_primeFactors
    (hT.symm ▸ hpprime.mem_primeFactors hpE Nat.card_pos.ne')
  have hint : T ⊓ K ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpT
    have hxproj : orderOf (π x.val) = 1 := by
      have hd : orderOf (π x.val) ∣ p :=
        by
          change orderOf (((π).comp T.subtype) x) ∣ p
          simpa only [hx] using orderOf_map_dvd ((π).comp T.subtype) x
      rcases (Nat.dvd_prime hpprime).mp hd with h | h
      · exact h
      · exact (hp (by simpa only [h] using orderOf_dvd_natCard (π x.val))).elim
    have hx1 : x.val = 1 := Subgroup.mem_bot.mp (hbot ▸
      (show x.val ∈ T ⊓ K from ⟨x.property, orderOf_eq_one_iff.mp hxproj⟩))
    have : x = 1 := Subtype.ext hx1
    exact hpprime.ne_one (by simpa [this] using hx.symm)
  have hmap : T.map π = ⊤ := by
    apply hG
    apply Finset.Subset.antisymm
    · exact Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card _) Nat.card_pos.ne'
    · intro q hq
      have hqprime := Nat.prime_of_mem_primeFactors hq
      have hqne : q ≠ p := fun heq ↦ hp (heq ▸ Nat.dvd_of_mem_primeFactors hq)
      have hqE : q ∣ Nat.card E :=
        (Nat.dvd_of_mem_primeFactors hq).trans (Subgroup.card_dvd_of_surjective rightHom_surjective)
      have hqT : q ∣ Nat.card T := Nat.dvd_of_mem_primeFactors
        (hT.symm ▸ hqprime.mem_primeFactors hqE Nat.card_pos.ne')
      let : Fact q.Prime := ⟨hqprime⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqT
      let f := (π).subgroupMap T
      have horder : orderOf (f x) = q := by
        have hd : orderOf (f x) ∣ q := by simpa only [hx] using orderOf_map_dvd f x
        rcases (Nat.dvd_prime hqprime).mp hd with h | h
        · exfalso
          have hker : x.val ∈ K :=
            congrArg Subtype.val (orderOf_eq_one_iff.mp h)
          have hdvd : q ∣ p := by
            rw [← hx, orderOf_dvd_iff_pow_eq_one]
            exact Subtype.ext (ker_pow_eq_one hker)
          exact hqne ((Nat.dvd_prime hpprime).mp hdvd |>.resolve_left hqprime.ne_one)
        · exact h
      apply hqprime.mem_primeFactors _ Nat.card_pos.ne'
      simpa only [horder] using orderOf_dvd_natCard (f x)
  have hKT : K ≤ T := ker_le_of_stable (fun g ↦ by
    have hg : g ∈ T.map π := hmap ▸ Subgroup.mem_top _
    obtain ⟨x, hx, hproj⟩ := hg
    exact ⟨x, hproj, T.le_normalizer hx⟩) hint
  rw [← Subgroup.comap_map_eq_self hKT, hmap, Subgroup.comap_top]

private lemma extension_solvable [Group.IsSolvable G] : Group.IsSolvable E :=
  Group.isSolvable_of_ker_le_range ι π range_inl_eq_ker_rightHom.ge

private lemma extension_has_common_element [Fact (Nat.Prime p)]
    [IsSimpleModule (ZMod p)[G] V] (hfaith : Function.Injective (algebraAction p G V)) :
    ∃ a : E, a ≠ 1 ∧ ∀ N : Subgroup E, N.Normal → N ≠ ⊥ → a ∈ N := by
  have : Nontrivial V := IsSimpleModule.nontrivial (ZMod p)[G] V
  obtain ⟨v, hv⟩ := exists_ne (1 : Multiplicative V)
  refine ⟨ι v, fun h ↦ hv (inl_injective (h.trans (map_one ι).symm)), ?_⟩
  intro N hnormal hne
  exact ker_le_of_normal hfaith hne (by simp)

end Extension

private lemma exists_group (h : ℕ) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), Group.IsSolvable G ∧ FullPrimeForcesTop G ∧
      ¬ FittingHeightLE G h ∧
      ∃ a : G, a ≠ 1 ∧ ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → a ∈ N := by
  induction h with
  | zero =>
    let G := Multiplicative (ZMod 2)
    have hc : Nat.card G = 2 := Nat.card_zmod _
    let : Fact (Nat.card G).Prime := ⟨hc ▸ Nat.prime_two⟩
    have : Nontrivial G := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hc]; decide)
    obtain ⟨a, ha⟩ := exists_ne (1 : G)
    refine ⟨G, inferInstance, inferInstance, inferInstance, ?_, ?_, a, ha, ?_⟩
    · intro T hT
      rcases T.eq_bot_or_eq_top_of_prime_card with rfl | htop
      · rw [Subgroup.card_bot, hc, Nat.primeFactors_one, Nat.prime_two.primeFactors] at hT
        simp at hT
      · exact htop
    · rintro ⟨s, hbot, htop, _⟩
      exact bot_ne_top (hbot.symm.trans htop)
    · intro N _ hne
      have hn := N.eq_bot_or_eq_top_of_prime_card.resolve_left hne
      rw [hn]
      exact Subgroup.mem_top _
  | succ h ih =>
    obtain ⟨G, _, _, hsol, hfull, hheight, a, ha, ha_mem⟩ := ih
    obtain ⟨p, hlt, hp⟩ := Nat.exists_infinite_primes (Nat.card G + 1)
    let : Fact p.Prime := ⟨hp⟩
    have hnd : ¬ p ∣ Nat.card G := fun hd ↦
      (Nat.not_le_of_lt hlt) (Nat.le_of_dvd Nat.card_pos hd)
    obtain ⟨S, hS, hfaith⟩ := exists_faithful_simple hnd a ha ha_mem
    have : Finite (ZMod p)[G] := Finite.of_injective
      (fun r : (ZMod p)[G] ↦ (r.coeff : G → ZMod p))
      (fun _ _ heq ↦ MonoidAlgebra.coeffEquiv.injective (DFunLike.coe_injective heq))
    have : Finite S := Finite.of_injective Subtype.val Subtype.val_injective
    let E := Multiplicative S ⋊[algebraAction p G S] G
    let : Finite E := Finite.of_equiv _ equivProd.symm
    refine ⟨E, inferInstance, inferInstance, extension_solvable,
      extension_fullPrimeForcesTop hnd hfull, ?_, extension_has_common_element hfaith⟩
    exact fun hh ↦ hheight (fittingHeight_of_extension hnd hfaith hh)

end

@[expose] public section

/--
**Moretó: soluble groups in Kourovka 19.55 have unbounded Fitting height.** For every natural
number $h$ there is a finite soluble group $G$ whose Fitting height is greater than $h$ and in
which every maximal subgroup $M$ with $\pi(M) = \pi(G)$ is supersoluble, where $\pi(X)$ is the set
of primes dividing the order of $X$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.55 (V. S.
Monakhov); resolution: A. Moretó, Finite groups whose maximal subgroups of order divisible by all
the primes are supersolvable, Monatsh. Math. 195 (2021), no. 3, 497-500 (arXiv:2010.04808),
Theorem A (every nonabelian simple group occurs as a composition factor), Theorem B (solvable
examples of arbitrarily large nilpotency length and rank) and Theorem C (the p-length is 1 for every
prime divisor p of |G|); Kourovka Archive, Problem 19.55, https://arxiv.org/abs/2010.04808.
-/
theorem fittingHeightUnbounded_holds : fittingHeightUnbounded := by
  intro h
  obtain ⟨G, _, _, hsol, hfull, hheight, _⟩ := exists_group h
  refine ⟨G, inferInstance, inferInstance, hsol, ?_, hheight⟩
  intro M hM hπ
  exact (hM.ne_top (hfull M hπ)).elim

end

end MathlibExt.GroupTheory.FullPrimeMaximalSupersolubleKourovka19Problem55Wanted
