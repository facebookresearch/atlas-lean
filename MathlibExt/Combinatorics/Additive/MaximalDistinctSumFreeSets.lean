/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.Additive.DistinctLinkGraph
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Preorder.Finite
import MathlibExt.GroupTheory.FiniteAbelian.SubgroupCount

/-!
# Maximal distinct sum-free sets in groups of type I

For a group of type I(p) with p ≥ 5, choosing one element from each negation pair in a largest
sum-free set gives the exponential lower bound on the number of maximal distinct sum-free sets.
-/

namespace MetaMathlibExt

/-- **Size of a largest sum-free subset.** Let $G$ be a set with an addition and $S \subseteq G$.
Write $\mu(S)$ for the supremum in $\mathbb{N}$ of the sizes of the finite sum-free subsets of
$S$ (sets $T$ with $x + y \notin T$ for all $x, y \in T$), taken to be $0$ if these sizes are
unbounded. For finite $S$ this is the largest size of a sum-free subset of $S$, and $\mu(G)$ is
the value for $S = G$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction (`μ(G)`) and Theorem 2. -/
@[expose] public noncomputable def largestSumFreeCard {G : Type*} [Add G] (S : Set G) : ℕ :=
  sSup {k | ∃ T : Finset G, (T : Set G) ⊆ S ∧ IsSumFreeSet (T : Set G) ∧ T.card = k}

/-- **Number of maximal distinct sum-free sets.** Let $G$ be a set with an addition. The number
$f^*_{\max}(G)$ is the number of subsets of $G$ that are maximal, with respect to inclusion, among
the distinct sum-free subsets of $G$, and it is $0$ if there are infinitely many such subsets.
Here $S \subseteq G$ is distinct sum-free if $x + y \notin S$ for all $x, y \in S$ such that $x$,
$y$ and $x + y$ are pairwise distinct.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, section "Maximal distinct sum-free subsets". -/
@[expose] public noncomputable def maxDistinctSumFreeCount (G : Type*) [Add G] : ℕ :=
  {S : Set G | Maximal IsDistinctSumFreeSet S}.ncard

/-- **Groups of type I(p).** Let $G$ be a finite set and $p$ a natural number. $G$ is of type
$\mathrm{I}(p)$ if $p$ is the smallest prime with $p \equiv 2 \pmod 3$ dividing $|G|$: that is,
$p$ is prime, $p \equiv 2 \pmod 3$, $p$ divides $|G|$, and $p \le q$ for every prime $q$ with
$q \equiv 2 \pmod 3$ that divides $|G|$.

Only the order of $G$ is used; in the paper $G$ is a finite abelian group.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 1. -/
@[expose] public def IsTypeOneGroup (G : Type*) [Fintype G] (p : ℕ) : Prop :=
  p.Prime ∧ p % 3 = 2 ∧ p ∣ Fintype.card G ∧
    ∀ q : ℕ, q.Prime → q % 3 = 2 → q ∣ Fintype.card G → p ≤ q

namespace two_rpow_le_maxDistinctSumFreeCount_of_typeOne

variable {G : Type*} [AddCommGroup G]

/-- The middle third of a cyclic quotient of order `3k + 2` lifts to a sum-free set of
density strictly greater than one third. -/
private theorem exists_dense [Fintype G] (p : ℕ) (hG : IsTypeOneGroup G p) :
    ∃ A : Finset G, IsSumFreeSet (A : Set G) ∧ Fintype.card G < 3 * A.card := by
  classical
  have : Fact p.Prime := ⟨hG.1⟩
  have : NeZero p := ⟨hG.1.ne_zero⟩
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card p hG.2.2.1
  have : Finite (AddSubgroup G) := Finite.of_injective _ SetLike.coe_injective
  have hpos : 0 < {H : AddSubgroup G | Nat.card H = p}.ncard :=
    (Set.ncard_pos (s := _)).mpr ⟨AddSubgroup.zmultiples g, (Nat.card_zmultiples g).trans hg⟩
  rw [ncard_addSubgroup_card_eq_ncard_index_eq] at hpos
  obtain ⟨H, hH⟩ := (Set.ncard_pos (s := _)).mp hpos
  change Nat.card (G ⧸ H) = p at hH
  have := isAddCyclic_of_prime_card hH
  let q : (G ⧸ H) ≃+ ZMod p := addEquivOfAddCyclicCardEq (hH.trans (Nat.card_zmod p).symm)
  -- Split the underlying set into equal-sized fibers of the quotient map.
  let e := (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := H)).trans
    (q.toEquiv.prodCongr (Equiv.refl H))
  let π := q.toAddMonoidHom.comp (QuotientAddGroup.mk' H)
  have proj (x : G) : (e x).1 = π x := rfl
  let k := p / 3
  have hpk : p = 3 * k + 2 := by
    have := hG.2.1
    dsimp [k]
    omega
  let mid (i : Fin (k + 1)) := ((i.val + k + 1 : ℕ) : ZMod p)
  have val_mid (i : Fin (k + 1)) : (mid i).val = i.val + k + 1 := by
    dsimp only [mid]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  let lift : Fin (k + 1) × H ↪ G := ⟨fun u ↦ e.symm (mid u.1, u.2), by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    obtain ⟨hij, rfl⟩ := Prod.mk.inj (e.symm.injective h)
    have hv : (mid i).val = (mid j).val := congrArg ZMod.val hij
    simp only [val_mid] at hv
    have hij : i = j := Fin.ext (by omega)
    exact Prod.ext hij rfl⟩
  let := Fintype.ofFinite H
  refine ⟨Finset.univ.map lift, ?_, ?_⟩
  · rintro x hx y hy hxy
    obtain ⟨⟨i, a⟩, -, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨⟨j, b⟩, -, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨⟨l, c⟩, -, heq⟩ := Finset.mem_map.mp hxy
    have first (i : Fin (k + 1)) (a : H) : π (lift (i, a)) = mid i := by
      rw [← proj]
      exact congrArg Prod.fst (e.apply_symm_apply _)
    have hv : mid l = mid i + mid j := calc
      mid l = π (lift (l, c)) := (first _ _).symm
      _ = π (lift (i, a) + lift (j, b)) := congrArg π heq
      _ = mid i + mid j := by rw [map_add, first, first]
    have hsum := congrArg ZMod.val hv
    by_cases h : (mid i).val + (mid j).val < p
    · rw [ZMod.val_add_of_lt h, val_mid, val_mid, val_mid] at hsum
      omega
    · rw [ZMod.val_add_of_le (by omega), val_mid, val_mid, val_mid] at hsum
      omega
  · have hc := Fintype.card_congr e
    simp only [Fintype.card_prod, ZMod.card] at hc
    simp only [Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    rw [hc, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right (by omega) Fintype.card_pos

/-- If more than a third of the group lies in `A`, the translations disjoint from `A` form
a symmetric sum-free set. A Schur triple of translations would give three disjoint copies. -/
private theorem symmetrize [Fintype G] (A : Finset G) (hA : IsSumFreeSet (A : Set G))
    (hd : Fintype.card G < 3 * A.card) :
    ∃ B : Finset G, A ⊆ B ∧ IsSumFreeSet (B : Set G) ∧ ∀ x ∈ B, -x ∈ B := by
  classical
  let shift (x : G) := A.map (Equiv.addLeft x).toEmbedding
  let B := Finset.univ.filter fun x ↦ ∀ y ∈ A, x + y ∉ A
  have mem {x : G} : x ∈ B ↔ ∀ y ∈ A, x + y ∉ A := by
    simp [B]
  refine ⟨B, fun x hx ↦ mem.mpr (hA x hx), ?_, ?_⟩
  · intro x hx y hy hxy
    have disj {t : G} (ht : t ∈ B) : Disjoint A (shift t) := by
      apply Finset.disjoint_left.mpr
      intro z hz h'z
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp h'z
      exact mem.mp ht a ha hz
    have d : Disjoint (shift x) (shift (x + y)) := by
      rw [Finset.disjoint_left]
      intro z hz h'z
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨b, hb, he⟩ := Finset.mem_map.mp h'z
      change x + y + b = x + a at he
      rw [add_assoc, add_right_inj] at he
      exact mem.mp hy b hb (he ▸ ha)
    have bound := (A ∪ shift x ∪ shift (x + y)).card_le_univ
    rw [Finset.card_union_of_disjoint (disjoint_sup_left.mpr ⟨disj hxy, d⟩),
      Finset.card_union_of_disjoint (disj hx)] at bound
    simp only [shift, Finset.card_map] at bound
    omega
  · intro x hx
    refine mem.mpr fun y hy h ↦ mem.mp hx (-x + y) h ?_
    simpa using hy

/-- Pick a sign for each representative. Every maximal extension containing the choices and zero
determines all the signs, since it cannot contain both members of a negation pair. -/
private theorem count_choices [Finite G] (B R : Finset G) (hB : IsSumFreeSet (B : Set G))
    (hR : ∀ r : R, (r : G) ∈ B ∧ -(r : G) ∈ B)
    (hsep : ∀ r s : R, (r : G) ≠ -(s : G)) :
    2 ^ R.card ≤ maxDistinctSumFreeCount G := by
  classical
  let := Fintype.ofFinite G
  let pick (f : R → Bool) (r : R) : G := if f r then r else -(r : G)
  have mem (f) (r) : pick f r ∈ B := by
    unfold pick
    split
    · exact (hR r).1
    · exact (hR r).2
  have nonzero {x : G} (hx : x ∈ B) : x ≠ 0 := by
    rintro rfl
    exact hB 0 hx 0 hx (by simpa using hx)
  have no_pair (f) (r s : R) : pick f r ≠ -pick f s := by
    by_cases he : r = s
    · subst s
      cases h : f r
      · simpa [pick, h] using (hsep r r).symm
      · simpa [pick, h] using hsep r r
    · have hne : (r : G) ≠ (s : G) := fun h ↦ he (Subtype.ext h)
      cases hr : f r <;> cases hs : f s <;>
        simp [pick, hr, hs, hne, hsep, Ne.symm (hsep s r)]
  let seed (f : R → Bool) := insert (0 : G) (Set.range (pick f))
  have free (f) : IsDistinctSumFreeSet (seed f) := by
    rintro x (rfl | ⟨r, rfl⟩) y (rfl | ⟨s, rfl⟩) hxy h₁ h₂ <;>
      try first | exact (h₁ (add_zero _)).elim | exact (h₂ (zero_add _)).elim
    rintro (h | ⟨t, ht⟩)
    · exact no_pair f r s (eq_neg_of_add_eq_zero_left h)
    · exact hB _ (mem f r) _ (mem f s) (ht ▸ mem f t)
  choose M hsub hmax using fun f ↦ Finite.exists_le_maximal (free f)
  have picked (f) (r) : pick f r ∈ M f := hsub f (Or.inr ⟨r, rfl⟩)
  have excluded (f) (r) : -pick f r ∉ M f := by
    have hn := nonzero (mem f r)
    intro h
    refine (hmax f).prop _ (picked f r) _ h (no_pair f r r) ?_ ?_ ?_
    · simpa using hn.symm
    · simpa using hn
    · simpa using hsub f (show (0 : G) ∈ seed f from Or.inl rfl)
  let extend (f : R → Bool) : {S : Set G | Maximal IsDistinctSumFreeSet S} := ⟨M f, hmax f⟩
  have inj : Function.Injective extend := by
    intro f g h
    have hM : M f = M g := congrArg Subtype.val h
    funext r
    by_contra hne
    have opp : pick f r = -pick g r := by
      cases hf : f r <;> cases hg : g r <;> simp_all [pick]
    exact excluded g r (opp ▸ hM ▸ picked f r)
  have bound := Fintype.card_le_of_injective extend inj
  rw [maxDistinctSumFreeCount, ← Set.fintypeCard_eq_ncard]
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using bound

/-- A finite symmetric sum-free set in an odd-order group splits into negation pairs. -/
private theorem count_symmetric [Fintype G] (B : Finset G) (hB : IsSumFreeSet (B : Set G))
    (hsym : ∀ x ∈ B, -x ∈ B) (hodd : ¬2 ∣ Fintype.card G) :
    (2 : ℝ) ^ ((B.card : ℝ) / 2) ≤ maxDistinctSumFreeCount G := by
  classical
  let e := Fintype.equivFin G
  let R := B.filter fun x ↦ e x < e (-x)
  have sep (r : R) : e r < e (-(r : G)) := (Finset.mem_filter.mp r.2).2
  have hfix {x : G} (hx : x ∈ B) : x ≠ -x := by
    intro he
    have hd : addOrderOf x ∣ 2 :=
      addOrderOf_dvd_of_nsmul_eq_zero (by rw [two_nsmul]; exact eq_neg_iff_add_eq_zero.mp he)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
    · obtain rfl := AddMonoid.addOrderOf_eq_one_iff.mp hone
      exact hB 0 hx 0 hx (by simpa using hx)
    · exact hodd (htwo ▸ addOrderOf_dvd_card (x := x))
  let negR := R.map (Equiv.neg G).toEmbedding
  have neg_mem {x : G} : x ∈ negR ↔ -x ∈ R := by simp [negR]
  have cover : R ∪ negR = B := by
    ext x
    rw [Finset.mem_union, neg_mem]
    by_cases hx : x ∈ B
    · have hne := fun he ↦ hfix hx (e.injective he)
      simp [R, hx, hsym x hx, lt_or_gt_of_ne hne]
    · have hn : -x ∉ B := fun hn ↦ hx (by simpa using hsym _ hn)
      simp [R, hx, hn]
  have hd : Disjoint R negR := by
    refine Finset.disjoint_left.mpr fun x hx hn ↦ ?_
    have hs := sep ⟨-x, neg_mem.mp hn⟩
    simp only [neg_neg] at hs
    exact (sep ⟨x, hx⟩).asymm hs
  have hc : B.card = R.card + R.card := by
    rw [← cover, Finset.card_union_of_disjoint hd, Finset.card_map]
  have bound := count_choices B R hB (fun r ↦
    let hr := (Finset.mem_filter.mp r.2).1
    ⟨hr, hsym _ hr⟩) (fun r s he ↦ by
      have h := sep r
      rw [he, neg_neg] at h
      exact h.asymm (sep s))
  rw [show (B.card : ℝ) / 2 = R.card by rw [hc, Nat.cast_add]; ring, Real.rpow_natCast]
  exact_mod_cast bound

end two_rpow_le_maxDistinctSumFreeCount_of_typeOne

/-- **Maximal distinct sum-free sets in groups of type $I(p)$.** Let $G$ be a finite abelian
group and let $p \ge 5$ be such that $G$ is of type $I(p)$, that is, $p$ is the smallest prime
with $p \equiv 2 \pmod 3$ that divides $|G|$. Call $S \subseteq G$ sum-free if $x + y \notin S$
for all $x, y \in S$, and distinct sum-free if $x + y \notin S$ for all $x, y \in S$ such that
$x$, $y$ and $x + y$ are pairwise distinct. Let $\mu(G)$ be the size of a largest sum-free subset
of $G$, and let $f^*_{\max}(G)$ be the number of maximal distinct sum-free subsets of $G$. Then
$f^*_{\max}(G) \ge 2^{\mu(G)/2}$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Proposition 1 (`integers-2026-A97-prop-1`). -/
public theorem two_rpow_le_maxDistinctSumFreeCount_of_typeOne {G : Type*}
    [AddCommGroup G] [Fintype G] {p : ℕ} (hp : 5 ≤ p) (hG : IsTypeOneGroup G p) :
    (2 : ℝ) ^ ((largestSumFreeCard (Set.univ : Set G) : ℝ) / 2) ≤ maxDistinctSumFreeCount G := by
  classical
  obtain ⟨D, hD, hd⟩ := two_rpow_le_maxDistinctSumFreeCount_of_typeOne.exists_dense p hG
  let sizes := {k | ∃ T : Finset G, (T : Set G) ⊆ Set.univ ∧
    IsSumFreeSet (T : Set G) ∧ T.card = k}
  have hmem : D.card ∈ sizes := ⟨D, Set.subset_univ _, hD, rfl⟩
  have hbdd : BddAbove sizes := by
    refine ⟨Fintype.card G, ?_⟩
    rintro k ⟨T, -, -, rfl⟩
    exact T.card_le_univ
  obtain ⟨A, -, hA, hc⟩ := Nat.sSup_mem (Set.nonempty_of_mem hmem) hbdd
  have hdA : Fintype.card G < 3 * A.card := by
    have := le_csSup hbdd hmem
    omega
  obtain ⟨B, hAB, hB, hsym⟩ :=
    two_rpow_le_maxDistinctSumFreeCount_of_typeOne.symmetrize A hA hdA
  have hodd : ¬2 ∣ Fintype.card G := fun h ↦ by
    have := hG.2.2.2 2 Nat.prime_two rfl h
    omega
  have hle : largestSumFreeCard (Set.univ : Set G) ≤ B.card :=
    calc
      sSup sizes = A.card := hc.symm
      _ ≤ B.card := Finset.card_le_card hAB
  apply le_trans _ (two_rpow_le_maxDistinctSumFreeCount_of_typeOne.count_symmetric B hB hsym hodd)
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) (by norm_num)

end MetaMathlibExt
