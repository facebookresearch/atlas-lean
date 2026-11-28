/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.ReplicatorStability

/-!
# Evolutionarily stable strategies in asymmetric two-role games (Selten's theorem)

`Domains.Biology.Dynamics.ReplicatorStability` treats **symmetric** matrix games, where every
contestant has the same strategy set and payoff matrix. In an **asymmetric** contest the two
contestants occupy distinguishable roles (owner and intruder, male and female, larger and
smaller): a contestant in role I chooses among strategies `ι` and earns `A i l` against a role-II
opponent playing `l`; a contestant in role II chooses among `κ` and earns `B k j` against a
role-I opponent playing `j`.

Following Selten (1980), a contestant is placed in role I with probability `ρ` and in role II with
probability `1 - ρ`, opposite an opponent in the other role. A **behavior strategy** is a pair
`(p, q)` of mixed strategies, `p` used in role I and `q` in role II, and the payoff of `(p, q)`
against `(p', q')` is

`rolePayoff ρ A B (p, q) (p', q') = ρ * (p · A q') + (1 - ρ) * (q · B p')`.

## Definitions

* `IsMixed p`: `p` is a mixed strategy (nonnegative, summing to `1`); this is the simplex
  condition used by `Replicator.IsESS`.
* `rolePayoff ρ A B s t`: the payoff of behavior strategy `s` against `t`.
* `IsRoleESS ρ A B s`: `s` is an evolutionarily stable behavior strategy, the Maynard Smith–Price
  conditions for `rolePayoff`.
* `IsStrictNash A B p q`: `(p, q)` is a strict Nash equilibrium of the bimatrix game `(A, B)`:
  every unilateral deviation in either role strictly lowers the deviator's payoff.
* `symmetrize ρ A B`: the symmetric matrix game on pure behavior strategies `ι × κ`, so that
  `Replicator.IsESS (symmetrize ρ A B)` is the symmetric-game ESS applied to the role game.

## Main results

* `isRoleESS_iff_isStrictNash` (**Selten's theorem**): for `0 < ρ < 1`, a behavior strategy is
  evolutionarily stable iff it is a strict Nash equilibrium of the bimatrix game.
* `IsStrictNash.exists_eq_single_left`, `IsStrictNash.exists_eq_single_right`: a strict Nash
  equilibrium is pure.
* `isStrictNash_single_iff`: the pure pair `(i, k)` is a strict Nash equilibrium iff `i` is the
  unique best reply to `k` and `k` the unique best reply to `i`.
* `IsRoleESS.exists_eq_single`: every ESS of a role game is a pair of pure strategies.
* `IsRoleESS.not_pos_left`: in contrast with the interior ESS of
  `ReplicatorStability`, a role game with at least two role-I strategies has no ESS that is
  completely mixed in role I (and symmetrically, `IsRoleESS.not_pos_right`).
* `dotProduct_symmetrize_mulVec`: payoffs in the symmetrized matrix game depend only on the
  marginal behavior strategies.
* `isESS_symmetrize_iff`: a mixed strategy `x` on `ι × κ` is an ESS of the symmetrized matrix game
  in the sense of `Replicator.IsESS` iff `x` is the point mass at a pure pair `(i, k)` that is a
  strict Nash equilibrium.

## Scope

The role probability is restricted to `0 < ρ < 1`. Both bounds are needed: at `ρ = 1` the role-II
strategy never affects any payoff, so a mutant that changes only its role-II behavior is neutral
and no behavior strategy is evolutionarily stable, even when a strict Nash equilibrium exists
(the tests exhibit this). Dynamics are not treated: the bimatrix replicator equation and the
non-asymptotic-stability of its interior rest points (Hofbauer–Sigmund 1998, Chapter 10) are
not proved here.

## Source receipt

* R. Selten, *A note on evolutionarily stable strategies in asymmetric animal conflicts*,
  J. Theoret. Biol. 84 (1980) 93–101 (ESS of a game with role asymmetries is a strict
  equilibrium, hence pure).
* J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge University
  Press (1998), Chapter 10 (bimatrix games; the symmetrized game with payoffs
  `p · A q' + q · B p'`, whose ESS are the strict Nash equilibria).
* J. Maynard Smith and G. A. Parker, *The logic of asymmetric contests*, Anim. Behav. 24 (1976)
  159–175.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Biology.Dynamics.AsymmetricESS

open MathlibExt.Biology.Dynamics.Replicator (IsESS)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Definitions -/

/-- `p` is a **mixed strategy**: its weights are nonnegative and sum to `1`. This is the simplex
condition used by `Replicator.IsNash` and `Replicator.IsESS`. -/
def IsMixed (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- **Mixed-strategy weights.** A finite strategy vector is mixed exactly when its weights
are nonnegative and sum to one. -/
theorem isMixed_iff {p : ι → ℝ} : IsMixed p ↔ (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 :=
  Iff.rfl

/-- The payoff of the behavior strategy `s = (p, q)` against `t = (p', q')` in the role game
where a contestant is in role I with probability `ρ` and in role II with probability `1 - ρ`:
`ρ * (p · A q') + (1 - ρ) * (q · B p')`. The expected-payoff reading needs `0 ≤ ρ ≤ 1` and mixed
strategies; the formula is defined for all vectors and all real `ρ`. -/
def rolePayoff (ρ : ℝ) (A : Matrix ι κ ℝ) (B : Matrix κ ι ℝ)
    (s t : (ι → ℝ) × (κ → ℝ)) : ℝ :=
  ρ * (s.1 ⬝ᵥ A *ᵥ t.2) + (1 - ρ) * (s.2 ⬝ᵥ B *ᵥ t.1)

/-- `s` is an **evolutionarily stable behavior strategy** of the role game (Selten 1980): `s` is
a pair of mixed strategies and every other pair `t` of mixed strategies either does strictly
worse against `s` than `s` itself, or does equally well against `s` and strictly worse against
`t` than `s` does. -/
def IsRoleESS (ρ : ℝ) (A : Matrix ι κ ℝ) (B : Matrix κ ι ℝ) (s : (ι → ℝ) × (κ → ℝ)) : Prop :=
  (IsMixed s.1 ∧ IsMixed s.2) ∧
    ∀ t : (ι → ℝ) × (κ → ℝ), IsMixed t.1 → IsMixed t.2 → t ≠ s →
      rolePayoff ρ A B t s < rolePayoff ρ A B s s ∨
        (rolePayoff ρ A B t s = rolePayoff ρ A B s s ∧
          rolePayoff ρ A B t t < rolePayoff ρ A B s t)

/-- `(p, q)` is a **strict Nash equilibrium** of the bimatrix game `(A, B)`: every other mixed
strategy of role I earns strictly less than `p` against `q`, and every other mixed strategy of
role II earns strictly less than `q` against `p`. -/
def IsStrictNash (A : Matrix ι κ ℝ) (B : Matrix κ ι ℝ) (p : ι → ℝ) (q : κ → ℝ) : Prop :=
  (IsMixed p ∧ IsMixed q) ∧
    (∀ p', IsMixed p' → p' ≠ p → p' ⬝ᵥ A *ᵥ q < p ⬝ᵥ A *ᵥ q) ∧
    ∀ q', IsMixed q' → q' ≠ q → q' ⬝ᵥ B *ᵥ p < q ⬝ᵥ B *ᵥ p

/-- The **symmetrized matrix game** of the role game: the pure strategies are the pure behavior
strategies `(i, k) ∈ ι × κ`, and `(i, k)` earns `ρ * A i l + (1 - ρ) * B k j` against `(j, l)`. -/
def symmetrize (ρ : ℝ) (A : Matrix ι κ ℝ) (B : Matrix κ ι ℝ) : Matrix (ι × κ) (ι × κ) ℝ :=
  Matrix.of fun a b => ρ * A a.1 b.2 + (1 - ρ) * B a.2 b.1

/-- The behavior strategy induced by a mixed strategy `x` on `ι × κ`: its role-I and role-II
marginals. -/
def marginals (x : ι × κ → ℝ) : (ι → ℝ) × (κ → ℝ) :=
  (fun i => ∑ k, x (i, k), fun k => ∑ i, x (i, k))

/-- The product `(i, k) ↦ p i * q k` on `ι × κ`; for mixed `p` and `q` it is a mixed strategy with
marginals `p` and `q`. -/
def prodStrategy (p : ι → ℝ) (q : κ → ℝ) : ι × κ → ℝ :=
  fun a => p a.1 * q a.2

/-! ### Mixed strategies and point masses -/

theorem isMixed_single [DecidableEq ι] (i : ι) : IsMixed (Pi.single i (1 : ℝ)) :=
  ⟨fun j => by by_cases hj : j = i <;> simp [hj], by simp⟩

/-- A mixed strategy other than the pure strategy `i` puts positive weight on some `j ≠ i`. -/
theorem IsMixed.exists_pos_of_ne_single [DecidableEq ι] {p : ι → ℝ} (hp : IsMixed p) {i : ι}
    (hne : p ≠ Pi.single i 1) : ∃ j, j ≠ i ∧ 0 < p j := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  apply hne
  have hzero : ∀ j, j ≠ i → p j = 0 := fun j hj => le_antisymm (h j hj) (hp.1 j)
  have hsum : ∑ j, p j = p i :=
    Finset.sum_eq_single i (fun j _ hj => hzero j hj) (fun hi => absurd (mem_univ i) hi)
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, ← hsum, hp.2]
  · rw [Pi.single_eq_of_ne hj, hzero j hj]

/-- Against a fixed payoff vector `v`, a mixed strategy earns at most the best pure payoff. -/
theorem IsMixed.dotProduct_le {p : ι → ℝ} (hp : IsMixed p) {v : ι → ℝ} {c : ℝ}
    (hv : ∀ j, v j ≤ c) : p ⬝ᵥ v ≤ c := by
  calc p ⬝ᵥ v = ∑ j, p j * v j := rfl
    _ ≤ ∑ j, p j * c := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hp.1 j)
    _ = c := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- If pure strategy `i` is the unique maximizer of `v`, every other mixed strategy earns
strictly less than `v i`. -/
theorem IsMixed.dotProduct_lt [DecidableEq ι] {p : ι → ℝ} (hp : IsMixed p) {v : ι → ℝ} {i : ι}
    (hv : ∀ j, j ≠ i → v j < v i) (hne : p ≠ Pi.single i 1) : p ⬝ᵥ v < v i := by
  obtain ⟨j, hji, hj⟩ := hp.exists_pos_of_ne_single hne
  calc p ⬝ᵥ v = ∑ l, p l * v l := rfl
    _ < ∑ l, p l * v i := by
        refine Finset.sum_lt_sum (fun l _ => ?_) ⟨j, mem_univ j, ?_⟩
        · by_cases hl : l = i
          · rw [hl]
          · exact mul_le_mul_of_nonneg_left (hv l hl).le (hp.1 l)
        · exact mul_lt_mul_of_pos_left (hv j hji) hj
    _ = v i := by rw [← Finset.sum_mul, hp.2, one_mul]

/-! ### Strict Nash equilibria -/

variable {ρ : ℝ} {A : Matrix ι κ ℝ} {B : Matrix κ ι ℝ} {p : ι → ℝ} {q : κ → ℝ}

theorem IsStrictNash.le_left (h : IsStrictNash A B p q) {p' : ι → ℝ} (hp' : IsMixed p') :
    p' ⬝ᵥ A *ᵥ q ≤ p ⬝ᵥ A *ᵥ q := by
  by_cases hpp : p' = p
  · rw [hpp]
  · exact (h.2.1 p' hp' hpp).le

theorem IsStrictNash.le_right (h : IsStrictNash A B p q) {q' : κ → ℝ} (hq' : IsMixed q') :
    q' ⬝ᵥ B *ᵥ p ≤ q ⬝ᵥ B *ᵥ p := by
  by_cases hqq : q' = q
  · rw [hqq]
  · exact (h.2.2 q' hq' hqq).le

/-- **A strict Nash equilibrium is pure in role I.** -/
theorem IsStrictNash.exists_eq_single_left [DecidableEq ι] (h : IsStrictNash A B p q) :
    ∃ i, p = Pi.single i 1 := by
  have hne : (univ : Finset ι).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    have := h.1.1.2
    rw [h0, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image univ (A *ᵥ q) hne
  refine ⟨i, ?_⟩
  by_contra hpi
  have hlt := h.2.1 _ (isMixed_single i) (Ne.symm hpi)
  rw [single_dotProduct, one_mul] at hlt
  exact absurd (h.1.1.dotProduct_le fun j => hi j (mem_univ j)) (not_le.2 hlt)

/-- **A strict Nash equilibrium is pure in role II.** -/
theorem IsStrictNash.exists_eq_single_right [DecidableEq κ] (h : IsStrictNash A B p q) :
    ∃ k, q = Pi.single k 1 := by
  have hne : (univ : Finset κ).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    have := h.1.2.2
    rw [h0, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image univ (B *ᵥ p) hne
  refine ⟨k, ?_⟩
  by_contra hqk
  have hlt := h.2.2 _ (isMixed_single k) (Ne.symm hqk)
  rw [single_dotProduct, one_mul] at hlt
  exact absurd (h.1.2.dotProduct_le fun l => hk l (mem_univ l)) (not_le.2 hlt)

/-- **Pure strict Nash equilibria.** The pure pair `(i, k)` is a strict Nash equilibrium iff `i`
is the unique best reply to `k` in role I and `k` is the unique best reply to `i` in role II. -/
theorem isStrictNash_single_iff [DecidableEq ι] [DecidableEq κ] (i : ι) (k : κ) :
    IsStrictNash A B (Pi.single i 1) (Pi.single k 1) ↔
      (∀ j, j ≠ i → A j k < A i k) ∧ ∀ l, l ≠ k → B l i < B k i := by
  have hA : ∀ p' : ι → ℝ, p' ⬝ᵥ A *ᵥ Pi.single k 1 = p' ⬝ᵥ fun j => A j k := fun p' => by
    rw [mulVec_single_one]; rfl
  have hB : ∀ q' : κ → ℝ, q' ⬝ᵥ B *ᵥ Pi.single i 1 = q' ⬝ᵥ fun l => B l i := fun q' => by
    rw [mulVec_single_one]; rfl
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨fun j hj => ?_, fun l hl => ?_⟩
    · have hne : (Pi.single j 1 : ι → ℝ) ≠ Pi.single i 1 := fun he => by
        have := congrFun he j
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hj] at this
        exact one_ne_zero this
      simpa [hA, single_dotProduct] using h1 _ (isMixed_single j) hne
    · have hne : (Pi.single l 1 : κ → ℝ) ≠ Pi.single k 1 := fun he => by
        have := congrFun he l
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hl] at this
        exact one_ne_zero this
      simpa [hB, single_dotProduct] using h2 _ (isMixed_single l) hne
  · rintro ⟨h1, h2⟩
    refine ⟨⟨isMixed_single i, isMixed_single k⟩, fun p' hp' hne => ?_, fun q' hq' hne => ?_⟩
    · rw [hA, hA, single_dotProduct, one_mul]
      exact hp'.dotProduct_lt h1 hne
    · rw [hB, hB, single_dotProduct, one_mul]
      exact hq'.dotProduct_lt h2 hne

/-! ### Selten's theorem -/

/-- **Selten's theorem** (Selten 1980; Hofbauer–Sigmund 1998, Chapter 10). In a role game where both
roles occur with positive probability, a behavior strategy is evolutionarily stable iff it is a
strict Nash equilibrium of the underlying bimatrix game. -/
theorem isRoleESS_iff_isStrictNash (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IsRoleESS ρ A B (p, q) ↔ IsStrictNash A B p q := by
  constructor
  · intro h
    refine ⟨h.1, fun p' hp' hne => ?_, fun q' hq' hne => ?_⟩
    · have hne' : ((p', q) : (ι → ℝ) × (κ → ℝ)) ≠ (p, q) := fun he =>
        hne (congrArg Prod.fst he)
      rcases h.2 (p', q) hp' h.1.2 hne' with h1 | ⟨-, h1⟩ <;>
        (simp only [rolePayoff] at h1; nlinarith)
    · have hne' : ((p, q') : (ι → ℝ) × (κ → ℝ)) ≠ (p, q) := fun he =>
        hne (congrArg Prod.snd he)
      rcases h.2 (p, q') h.1.1 hq' hne' with h1 | ⟨-, h1⟩ <;>
        (simp only [rolePayoff] at h1; nlinarith)
  · intro h
    refine ⟨h.1, fun t ht1 ht2 hne => Or.inl ?_⟩
    simp only [rolePayoff]
    have hA := h.le_left ht1
    have hB := h.le_right ht2
    by_cases h1 : t.1 = p
    · have h2 : t.2 ≠ q := fun h2 => hne (Prod.ext h1 h2)
      have hlt := h.2.2 t.2 ht2 h2
      nlinarith
    · have hlt := h.2.1 t.1 ht1 h1
      nlinarith

/-- **Every ESS of a role game is pure** in both roles, for `0 < ρ < 1`. -/
theorem IsRoleESS.exists_eq_single [DecidableEq ι] [DecidableEq κ] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h : IsRoleESS ρ A B (p, q)) : ∃ i k, p = Pi.single i 1 ∧ q = Pi.single k 1 := by
  have hs := (isRoleESS_iff_isStrictNash hρ0 hρ1).1 h
  obtain ⟨i, hi⟩ := hs.exists_eq_single_left
  obtain ⟨k, hk⟩ := hs.exists_eq_single_right
  exact ⟨i, k, hi, hk⟩

/-- **No completely mixed ESS in role I.** For `0 < ρ < 1` and at least two role-I strategies,
an ESS of a role game never uses every role-I strategy, unlike the interior ESS of a symmetric
game. -/
theorem IsRoleESS.not_pos_left [Nontrivial ι] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h : IsRoleESS ρ A B (p, q)) : ¬ ∀ i, 0 < p i := by
  classical
  intro hpos
  obtain ⟨i, k, hi, -⟩ := h.exists_eq_single hρ0 hρ1
  obtain ⟨j, hj⟩ := exists_ne i
  have := hpos j
  rw [hi, Pi.single_eq_of_ne hj] at this
  exact lt_irrefl 0 this

/-- **No completely mixed ESS in role II.** For `0 < ρ < 1` and at least two role-II strategies,
an ESS of a role game never uses every role-II strategy. -/
theorem IsRoleESS.not_pos_right [Nontrivial κ] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h : IsRoleESS ρ A B (p, q)) : ¬ ∀ k, 0 < q k := by
  classical
  intro hpos
  obtain ⟨i, k, -, hk⟩ := h.exists_eq_single hρ0 hρ1
  obtain ⟨l, hl⟩ := exists_ne k
  have := hpos l
  rw [hk, Pi.single_eq_of_ne hl] at this
  exact lt_irrefl 0 this

/-! ### The symmetrized matrix game -/

/-- **Payoffs in the symmetrized game depend only on marginals**: the payoff of `x` against `y`
in the matrix game `symmetrize ρ A B` is the role-game payoff of their marginal behavior
strategies. -/
theorem dotProduct_symmetrize_mulVec (x y : ι × κ → ℝ) :
    x ⬝ᵥ symmetrize ρ A B *ᵥ y = rolePayoff ρ A B (marginals x) (marginals y) := by
  have h1 : (marginals x).1 ⬝ᵥ A *ᵥ (marginals y).2 =
      ∑ i, ∑ k, ∑ j, ∑ l, x (i, k) * (A i l * y (j, l)) := by
    simp only [marginals, dotProduct, mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have h2 : (marginals x).2 ⬝ᵥ B *ᵥ (marginals y).1 =
      ∑ i, ∑ k, ∑ j, ∑ l, x (i, k) * (B k j * y (j, l)) := by
    simp only [marginals, dotProduct, mulVec, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [rolePayoff, h1, h2]
  simp only [symmetrize, dotProduct, mulVec, of_apply, Fintype.sum_prod_type, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isMixed_marginals {x : ι × κ → ℝ} (hx : IsMixed x) :
    IsMixed (marginals x).1 ∧ IsMixed (marginals x).2 := by
  refine ⟨⟨fun i => Finset.sum_nonneg fun k _ => hx.1 (i, k), ?_⟩,
    ⟨fun k => Finset.sum_nonneg fun i _ => hx.1 (i, k), ?_⟩⟩
  · simp only [marginals]
    rw [← hx.2, Fintype.sum_prod_type]
  · simp only [marginals]
    rw [Finset.sum_comm, ← hx.2, Fintype.sum_prod_type]

theorem isMixed_prodStrategy (hp : IsMixed p) (hq : IsMixed q) : IsMixed (prodStrategy p q) := by
  refine ⟨fun a => mul_nonneg (hp.1 a.1) (hq.1 a.2), ?_⟩
  simp only [prodStrategy, Fintype.sum_prod_type, ← Finset.mul_sum, hq.2, mul_one,
    hp.2]

theorem marginals_prodStrategy (hp : IsMixed p) (hq : IsMixed q) :
    marginals (prodStrategy p q) = (p, q) := by
  refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
  · simp only [marginals, prodStrategy, ← Finset.mul_sum, hq.2, mul_one]
  · simp only [marginals, prodStrategy, ← Finset.sum_mul, hp.2, one_mul]

omit [Fintype ι] [Fintype κ] in
theorem single_eq_prodStrategy [DecidableEq ι] [DecidableEq κ] (i : ι) (k : κ) :
    (Pi.single (i, k) 1 : ι × κ → ℝ) = prodStrategy (Pi.single i 1) (Pi.single k 1) := by
  funext a
  obtain ⟨j, l⟩ := a
  simp only [prodStrategy, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem marginals_single [DecidableEq ι] [DecidableEq κ] (i : ι) (k : κ) :
    marginals (Pi.single (i, k) 1 : ι × κ → ℝ) = (Pi.single i 1, Pi.single k 1) := by
  rw [single_eq_prodStrategy]
  exact marginals_prodStrategy (isMixed_single i) (isMixed_single k)

/-- A mixed strategy on `ι × κ` whose marginals are the pure strategies `i` and `k` is the point
mass at `(i, k)`. -/
theorem IsMixed.eq_single_of_marginals [DecidableEq ι] [DecidableEq κ] {x : ι × κ → ℝ}
    (hx : IsMixed x) {i : ι} {k : κ}
    (hm : marginals x = (Pi.single i 1, Pi.single k 1)) : x = Pi.single (i, k) 1 := by
  have hzero : ∀ a : ι × κ, a ≠ (i, k) → x a = 0 := by
    rintro ⟨j, l⟩ hne
    refine le_antisymm ?_ (hx.1 _)
    by_cases hj : j = i
    · have hl : l ≠ k := fun hl => hne (by rw [hj, hl])
      have h2 := congrFun (congrArg Prod.snd hm) l
      simp only [marginals, Pi.single_eq_of_ne hl] at h2
      rw [← h2]
      exact Finset.single_le_sum (f := fun j' => x (j', l)) (fun j' _ => hx.1 _) (mem_univ j)
    · have h1 := congrFun (congrArg Prod.fst hm) j
      simp only [marginals, Pi.single_eq_of_ne hj] at h1
      rw [← h1]
      exact Finset.single_le_sum (f := fun l' => x (j, l')) (fun l' _ => hx.1 _) (mem_univ l)
  have hsum : ∑ a, x a = x (i, k) :=
    Finset.sum_eq_single (i, k) (fun a _ ha => hzero a ha) (fun h => absurd (mem_univ _) h)
  funext a
  by_cases ha : a = (i, k)
  · rw [ha, Pi.single_eq_same, ← hsum, hx.2]
  · rw [Pi.single_eq_of_ne ha, hzero a ha]

/-- **The symmetric-game ESS of the symmetrized role game** (Hofbauer–Sigmund 1998, Ch. 10). For
`0 < ρ < 1`, a mixed strategy `x` on the pure behavior strategies `ι × κ` is an ESS of the matrix
game `symmetrize ρ A B` in the sense of `Replicator.IsESS` iff `x` is the point mass at a pure
pair `(i, k)` that is a strict Nash equilibrium of the bimatrix game. -/
theorem isESS_symmetrize_iff [DecidableEq ι] [DecidableEq κ] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (x : ι × κ → ℝ) :
    IsESS (symmetrize ρ A B) x ↔
      ∃ i k, x = Pi.single (i, k) 1 ∧ IsStrictNash A B (Pi.single i 1) (Pi.single k 1) := by
  constructor
  · intro h
    have hx : IsMixed x := h.1
    have hrole : IsRoleESS ρ A B (marginals x) := by
      refine ⟨isMixed_marginals hx, fun t ht1 ht2 hne => ?_⟩
      have hy := isMixed_prodStrategy ht1 ht2
      have hmy : marginals (prodStrategy t.1 t.2) = t := marginals_prodStrategy ht1 ht2
      have hyx : prodStrategy t.1 t.2 ≠ x := fun he => hne (by rw [← hmy, he])
      have := h.2 (prodStrategy t.1 t.2) hy hyx
      simpa only [dotProduct_symmetrize_mulVec, hmy] using this
    have hs := (isRoleESS_iff_isStrictNash hρ0 hρ1).1 hrole
    obtain ⟨i, hi⟩ := hs.exists_eq_single_left
    obtain ⟨k, hk⟩ := hs.exists_eq_single_right
    have hm : marginals x = (Pi.single i 1, Pi.single k 1) := Prod.ext hi hk
    refine ⟨i, k, hx.eq_single_of_marginals hm, ?_⟩
    rw [← hi, ← hk]
    exact hs
  · rintro ⟨i, k, rfl, hs⟩
    have hrole := (isRoleESS_iff_isStrictNash hρ0 hρ1).2 hs
    refine ⟨isMixed_single (i, k), fun y hy hne => ?_⟩
    have hy' : IsMixed y := hy
    have hmy := isMixed_marginals hy'
    have hne' : marginals y ≠ (Pi.single i 1, Pi.single k 1) := fun he =>
      hne (hy'.eq_single_of_marginals he)
    have := hrole.2 (marginals y) hmy.1 hmy.2 hne'
    simpa only [dotProduct_symmetrize_mulVec, marginals_single] using this

end MathlibExt.Biology.Dynamics.AsymmetricESS
