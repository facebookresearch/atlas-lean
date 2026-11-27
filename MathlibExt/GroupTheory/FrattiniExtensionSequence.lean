/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Frattini

/-!
# Infinite chains of Frattini extensions of finite `p`-groups

Every nontrivial finite `p`-group starts an infinite chain of Φ-extensions
(`phiExtensionSequence_holds`). For one step, pull back a cyclic quotient of
largest order along the reduction from the next larger cyclic `p`-group.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FrattiniExtensionSequenceKourovka16Problem12Wanted

/-- **$\Phi$-extension (Berkovich).** For a natural number $p$ and groups $H$ and $G$, $H$ is a
$\Phi$-extension of $G$ when $H$ is a finite $p$-group with a normal subgroup $N$ of order $p$
such that $N \le \Phi(H)$, where $\Phi(H)$ is the Frattini subgroup of $H$, and $H/N \cong G$. -/
def IsPhiExtension (p : ℕ) (H G : Type) [Group H] [Group G] : Prop :=
  Finite H ∧ IsPGroup p H ∧ ∃ N : Subgroup H, ∃ _ : N.Normal,
    Nat.card N = p ∧ N ≤ frattini H ∧ Nonempty (H ⧸ N ≃* G)

/-- **Kourovka Problem 16.12 (infinite chains of $\Phi$-extensions).** The statement, a question
of Ya. G. Berkovich, that for every prime $p$ and every nontrivial finite $p$-group $G$ there are
groups $G_0, G_1, G_2, \dots$ with $G_0 \cong G$ such that, for every $i \ge 0$, $G_{i+1}$ is a
$\Phi$-extension of $G_i$ for the prime $p$. -/
def phiExtensionSequence : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G → Nontrivial G →
    ∃ (S : ℕ → Type) (_ : ∀ i, Group (S i)), Nonempty (S 0 ≃* G) ∧
      ∀ i, IsPhiExtension p (S (i + 1)) (S i)

private abbrev CyclicMod (n : ℕ) := Multiplicative (ZMod n)

private theorem card_cyclicMod (n : ℕ) [NeZero n] : Nat.card (CyclicMod n) = n := by
  simp [CyclicMod, Nat.card_eq_fintype_card]

/-- Choose a nontrivial cyclic quotient of largest order among the cyclic quotients of `G`. -/
private theorem maximal_cyclic_quotient {p : ℕ} [hp : Fact p.Prime]
    {G : Type} [Group G] [Finite G] [Nontrivial G] (hG : IsPGroup p G) :
    ∃ k > 0, (∃ f : G →* CyclicMod (p ^ k), Function.Surjective f) ∧
      ¬ ∃ t : G →* CyclicMod (p ^ (k + 1)), Function.Surjective t := by
  classical
  let Q (k : ℕ) := ∃ f : G →* CyclicMod (p ^ k), Function.Surjective f
  have bound {k : ℕ} (hk : Q k) : k ≤ Nat.card G := by
    obtain ⟨f, hf⟩ := hk
    have hcard := Nat.card_le_card_of_surjective f hf
    rw [card_cyclicMod] at hcard
    exact (Nat.lt_pow_self hp.out.one_lt).le.trans hcard
  have h₁ : Q 1 := by
    have := hG.isNilpotent
    have hd := hG.card_eq_or_dvd.resolve_left (Finite.one_lt_card (α := G)).ne'
    obtain ⟨M, hM, hnormal⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hd
    let e : G ⧸ M ≃* CyclicMod p :=
      mulEquivOfPrimeCardEq (M.index_eq_card.symm.trans hM) (card_cyclicMod p)
    dsimp only [Q]
    rw [pow_one]
    exact ⟨e.toMonoidHom.comp (QuotientGroup.mk' M),
      e.surjective.comp (QuotientGroup.mk'_surjective M)⟩
  let k := Nat.findGreatest Q (Nat.card G)
  have hmax {j : ℕ} (hj : Q j) : j ≤ k := Nat.le_findGreatest (bound hj) hj
  exact ⟨k, hmax h₁, Nat.findGreatest_spec (bound h₁) h₁,
    fun h => (Nat.not_succ_le_self k) (hmax h)⟩

/-- A lift to a cyclic group is surjective if it surjects after reduction and the order
of the reduction kernel divides the order of the quotient. -/
private theorem surjective_cyclic_lift {A B X : Type} [Group A] [Group B] [Group X]
    [Finite B] [IsCyclic B] (q : B →* A) (t : X →* B) (ht : Function.Surjective (q.comp t))
    (hd : Nat.card q.ker ∣ Nat.card A) : Function.Surjective t := by
  have hr : Function.Surjective (q.domRestrict t.range) := by
    intro a
    obtain ⟨x, hx⟩ := ht a
    exact ⟨⟨t x, x, rfl⟩, hx⟩
  have hle : q.ker ≤ t.range := IsCyclic.subgroup_le_iff_card_dvd.mpr
    (hd.trans (Subgroup.card_dvd_of_surjective hr))
  apply MonoidHom.range_eq_top.mp
  rw [← Subgroup.comap_map_eq_self hle, MonoidHom.map_range,
    MonoidHom.range_eq_top.mpr ht, Subgroup.comap_top]

/-- The pullback of the maximal cyclic quotient along its order-`p` enlargement gives
one Φ-extension. A maximal subgroup missing the kernel would lift the cyclic quotient. -/
private theorem exists_phiExtension {p : ℕ} [hp : Fact p.Prime]
    {G : Type} [Group G] [Finite G] [Nontrivial G] (hG : IsPGroup p G) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsPhiExtension p H G := by
  obtain ⟨k, hk, ⟨f, hf⟩, hmax⟩ := maximal_cyclic_quotient hG
  let A := CyclicMod (p ^ k)
  let B := CyclicMod (p ^ (k + 1))
  have hd : p ^ k ∣ p ^ (k + 1) := pow_dvd_pow p (Nat.le_succ k)
  let q : B →* A := AddMonoidHom.toMultiplicative (ZMod.castHom hd _).toAddMonoidHom
  have hq : Function.Surjective q := ZMod.castHom_surjective hd
  have hqcard : Nat.card q.ker = p := by
    have h := Subgroup.card_ker_mul_card_of_surjective hq
    change Nat.card q.ker * Nat.card (CyclicMod _) = Nat.card (CyclicMod _) at h
    rw [card_cyclicMod, card_cyclicMod] at h
    exact Nat.mul_right_cancel (pow_pos hp.out.pos _) (h.trans (pow_succ' p k))
  let H := (f.comp (MonoidHom.fst G B)).eqLocus (q.comp (MonoidHom.snd G B))
  let π : H →* G := (MonoidHom.fst G B).domRestrict H
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨b, hb⟩ := hq (f g)
    exact ⟨⟨(g, b), hb.symm⟩, rfl⟩
  -- The projection kernel consists of the pairs (1, b) for b in the reduction kernel.
  let eKer : π.ker ≃ q.ker :=
    { toFun x := ⟨x.1.1.2, x.1.2.symm.trans ((congrArg f x.2).trans f.map_one)⟩
      invFun b := ⟨⟨(1, b.1), f.map_one.trans b.2.symm⟩, rfl⟩
      left_inv x := Subtype.ext (Subtype.ext (Prod.ext x.2.symm rfl))
      right_inv _ := rfl }
  have hker : Nat.card π.ker = p := (Nat.card_congr eKer).trans hqcard
  have hcard := Subgroup.card_ker_mul_card_of_surjective hπ
  rw [hker] at hcard
  have hH : IsPGroup p H := by
    obtain ⟨n, hn⟩ := hG.exists_card_eq
    exact IsPGroup.of_card (n := n + 1) (by rw [← hcard, hn, pow_succ'])
  refine ⟨H, inferInstance, hπ.nontrivial, inferInstance, hH, π.ker, inferInstance, hker, ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective π hπ⟩⟩
  apply le_iInf₂
  intro M hM
  change IsCoatom M at hM
  by_contra hmiss
  -- Missing the kernel forces M to project onto G. Its index p then gives M ≃* G.
  have hsup := hM.2 _ (left_lt_sup.mpr hmiss)
  have hsurj : Function.Surjective (π.domRestrict M) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.domRestrict_range]
    apply Subgroup.comap_injective hπ
    rw [Subgroup.comap_map_eq, Subgroup.comap_top, hsup]
  have := hH.isNilpotent
  have hindex := hH.isCoatom_iff_index_eq_prime.mp hM
  have hsize := M.index_mul_card
  rw [hindex, ← hcard] at hsize
  let e := MulEquiv.ofBijective (π.domRestrict M)
    (hsurj.bijective_of_nat_card_le (Nat.mul_left_cancel hp.out.pos hsize).le)
  -- The second projection now lifts the quotient of G to the larger cyclic group.
  let t := ((MonoidHom.snd G B).domRestrict H).domRestrict M
  have ht : Function.Surjective (q.comp t) := by
    intro a
    obtain ⟨g, rfl⟩ := hf a
    obtain ⟨x, rfl⟩ := hsurj g
    exact ⟨x, x.1.2.symm⟩
  have hdker : Nat.card q.ker ∣ Nat.card A := by
    rw [hqcard, show Nat.card A = p ^ k from card_cyclicMod _]
    exact dvd_pow_self p hk.ne'
  exact hmax ⟨t.comp e.symm.toMonoidHom, (surjective_cyclic_lift q t ht hdker).comp
    e.symm.surjective⟩

private structure ChainTerm (p : ℕ) where
  carrier : Type
  [group : Group carrier]
  [finite : Finite carrier]
  [nontrivial : Nontrivial carrier]
  isPGroup : IsPGroup p carrier

attribute [local instance] ChainTerm.group ChainTerm.finite ChainTerm.nontrivial

/--
**Infinite chains of $\Phi$-extensions (Kourovka 16.12).** For every prime $p$ and every
nontrivial finite $p$-group $G$ there are groups $G_0, G_1, G_2, \dots$ with $G_0 \cong G$ such
that, for every $i \ge 0$, $G_{i+1}$ is a $\Phi$-extension of $G_i$ for the prime $p$. This answers
Kourovka Problem 16.12 in the affirmative: the Kourovka Archive answers "Yes, it is", citing
Kamornikov (2008).

The trivial group is excluded: it has no $\Phi$-extension, since a group of order $p$ has trivial
Frattini subgroup.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.12
(Ya. G. Berkovich); resolution: S. F. Kamornikov, Izv. Gomel' Univ. 5 (2008), 200-201 (Russian),
Kourovka Archive, Problem 16.12 (Yes, it is).
-/
theorem phiExtensionSequence_holds : phiExtensionSequence := by
  intro p hp G _ _ hG hnt
  have : Fact p.Prime := ⟨hp⟩
  have step (X : ChainTerm p) : ∃ Y : ChainTerm p, IsPhiExtension p Y.carrier X.carrier := by
    obtain ⟨H, inst, hn, h⟩ := exists_phiExtension X.isPGroup
    exact ⟨@ChainTerm.mk p H inst h.1 hn h.2.1, h⟩
  choose next hnext using step
  let S : ℕ → ChainTerm p := Nat.rec (ChainTerm.mk G hG) (fun _ => next)
  exact ⟨fun i => (S i).carrier, fun i => (S i).group, ⟨MulEquiv.refl G⟩, fun i => hnext (S i)⟩

end MathlibExt.GroupTheory.FrattiniExtensionSequenceKourovka16Problem12Wanted
