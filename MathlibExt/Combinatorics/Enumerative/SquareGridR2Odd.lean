/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GridReflectionTilings

/-!
# Square-grid tilings fixed by the half-turn for odd $n$

For positive odd $n$, a finite set $T$ of tile designs with decidable equality and a
permutation $\sigma$ of $T$ with $\sigma^2=1$, `MetaMathlibExt.squareGrid_r2_odd` counts the
tilings of the $n \times n$ grid fixed by the half-turn and $\sigma$. The nonfixed cells form
pairs, and the unique fixed cell must carry a tile fixed by $\sigma$.

The proof applies `fixedTilingsEquiv` to the half-turn and a choice of one cell from each
nonfixed pair.

## References

* Peter Kagey and William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
  Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 20 (p. 12) and
  Theorem 24, Equation (8) (p. 15).
-/

namespace MetaMathlibExt

namespace squareGrid_r2_odd

/-- The half-turn on the odd square grid, in `Fin` coordinates. -/
private def halfTurn (k : ℕ) (c : Fin (2 * k + 1) × Fin (2 * k + 1)) :
    Fin (2 * k + 1) × Fin (2 * k + 1) := (c.1.rev, c.2.rev)

/-- One representative from each half-turn pair: the first coordinate is on the
left, or it is the middle coordinate and the second is on the left. -/
private def repPred (k : ℕ) (c : Fin (2 * k + 1) × Fin (2 * k + 1)) : Prop :=
  c.1.val < k ∨ (c.1.val = k ∧ c.2.val < k)

private instance (k : ℕ) : DecidablePred (repPred k) :=
  fun c => by unfold repPred; infer_instance

private theorem halfTurn_involutive (k : ℕ) :
    Function.Involutive (halfTurn k) := fun ⟨x, y⟩ =>
  Prod.ext (Fin.rev_rev x) (Fin.rev_rev y)

private theorem rev_val (k : ℕ) (x : Fin (2 * k + 1)) :
    x.rev.val = 2 * k - x.val := by
  have h := Fin.add_rev_cast x
  omega

private theorem halfTurn_fixed_val (k : ℕ) {c : Fin (2 * k + 1) × Fin (2 * k + 1)}
    (h : halfTurn k c = c) : c.1.val = k ∧ c.2.val = k := by
  have hx : c.1.rev = c.1 := congrArg Prod.fst h
  have hy : c.2.rev = c.2 := congrArg Prod.snd h
  have hx' : c.1.rev.val = c.1.val := congrArg Fin.val hx
  have hy' : c.2.rev.val = c.2.val := congrArg Fin.val hy
  rw [rev_val] at hx' hy'
  have h1 := c.1.isLt
  have h2 := c.2.isLt
  omega

private theorem repPred_of_fixed (k : ℕ) {c : Fin (2 * k + 1) × Fin (2 * k + 1)}
    (h : halfTurn k c = c) : ¬ repPred k c := by
  obtain ⟨h1, h2⟩ := halfTurn_fixed_val k h
  unfold repPred
  omega

private theorem repPred_flip (k : ℕ) {c : Fin (2 * k + 1) × Fin (2 * k + 1)}
    (hne : halfTurn k c ≠ c) : repPred k (halfTurn k c) ↔ ¬ repPred k c := by
  have hnk : ¬ (c.1.val = k ∧ c.2.val = k) := by
    intro h
    apply hne
    obtain ⟨h1, h2⟩ := h
    have e1 : c.1.rev = c.1 := Fin.ext (by rw [rev_val]; omega)
    have e2 : c.2.rev = c.2 := Fin.ext (by rw [rev_val]; omega)
    exact Prod.ext e1 e2
  have hr1 : (halfTurn k c).1.val = 2 * k - c.1.val := by
    change c.1.rev.val = _; rw [rev_val]
  have hr2 : (halfTurn k c).2.val = 2 * k - c.2.val := by
    change c.2.rev.val = _; rw [rev_val]
  have h1 := c.1.isLt
  have h2 := c.2.isLt
  unfold repPred at *
  rw [hr1, hr2]
  omega

end squareGrid_r2_odd

/-- **Square-grid tilings fixed by the half-turn for odd $n$.** Let $n$ be an odd positive
integer, let $T$ be a finite set, let $\sigma$ be a permutation of $T$ with $\sigma^2 = 1$, and
write $t_\sigma$ for the number of elements $t \in T$ with $\sigma(t) = t$. Let $r^2$ be the
half-turn of the grid $(\mathbb{Z}/n\mathbb{Z})^2$ given by $r^2(x, y) = (-1 - x, -1 - y)$.
Then the number of maps $F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$ with $F(r^2(c)) = \sigma(F(c))$
for every cell $c$ is $|T|^{(n^2 - 1)/2} \cdot t_\sigma$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 24. -/
public theorem squareGrid_r2_odd {T : Type*} [Fintype T] [DecidableEq T]
    (n : ℕ) [NeZero n] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1) (hodd : Odd n) :
    fixedTilingCount (cellR2 n n) σ =
      Fintype.card T ^ ((n ^ 2 - 1) / 2) * tileFixedCount σ 1 := by
  obtain ⟨k, rfl⟩ := hodd
  have htiles : Function.Involutive σ := fun t => by
    simpa [sq] using DFunLike.congr_fun hσ t
  have hrev (x : Fin (2 * k + 1)) : -1 - x = x.rev := by
    rw [← Fin.last_sub, show (-1 : Fin (2 * k + 1)) = Fin.last (2 * k) from
      Fin.ext Fin.coe_neg_one]
  unfold fixedTilingCount
  change Fintype.card {F : Fin (2 * k + 1) × Fin (2 * k + 1) → T //
    ∀ c, F (-1 - c.1, -1 - c.2) = σ (F c)} = _
  simp_rw [hrev]
  change Fintype.card {F : Fin (2 * k + 1) × Fin (2 * k + 1) → T //
    ∀ c, F (squareGrid_r2_odd.halfTurn k c) = σ (F c)} = _
  -- The half-turn bijects representatives with the other halves of the pairs.
  have eAB : Subtype (squareGrid_r2_odd.repPred k) ≃
      {c // ¬ squareGrid_r2_odd.repPred k c ∧ squareGrid_r2_odd.halfTurn k c ≠ c} :=
    { toFun := fun a => ⟨squareGrid_r2_odd.halfTurn k a.1,
        ⟨fun h => (squareGrid_r2_odd.repPred_flip k
          (fun he => squareGrid_r2_odd.repPred_of_fixed k he a.2)).1 h a.2,
          by rw [squareGrid_r2_odd.halfTurn_involutive k a.1]
             exact Ne.symm (fun he =>
               squareGrid_r2_odd.repPred_of_fixed k he a.2)⟩⟩
      invFun := fun b => ⟨squareGrid_r2_odd.halfTurn k b.1,
        (squareGrid_r2_odd.repPred_flip k b.2.2).2 b.2.1⟩
      left_inv := fun a => Subtype.ext (squareGrid_r2_odd.halfTurn_involutive k a.1)
      right_inv := fun b => Subtype.ext (squareGrid_r2_odd.halfTurn_involutive k b.1) }
  have hAB : Fintype.card (Subtype (squareGrid_r2_odd.repPred k)) =
      Fintype.card {c // ¬ squareGrid_r2_odd.repPred k c ∧
        squareGrid_r2_odd.halfTurn k c ≠ c} := Fintype.card_congr eAB
  -- The fixed cell is unique.
  have hS : Fintype.card {c : Fin (2 * k + 1) × Fin (2 * k + 1) //
      squareGrid_r2_odd.halfTurn k c = c} = 1 := by
    have e : {c : Fin (2 * k + 1) × Fin (2 * k + 1) //
        squareGrid_r2_odd.halfTurn k c = c} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨(⟨k, by omega⟩, ⟨k, by omega⟩), by
          have e1 : (⟨k, by omega⟩ : Fin (2 * k + 1)).rev = ⟨k, by omega⟩ :=
            Fin.ext (by simp [Fin.rev]; omega)
          have e2 : (⟨k, by omega⟩ : Fin (2 * k + 1)).rev = ⟨k, by omega⟩ :=
            Fin.ext (by simp [Fin.rev]; omega)
          exact Prod.ext e1 e2⟩
        left_inv := fun s => by
          obtain ⟨h1, h2⟩ := squareGrid_r2_odd.halfTurn_fixed_val k s.2
          dsimp only
          exact Subtype.ext (Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm))
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_unit]
  -- Every cell is a representative, a non-representative in a pair, or fixed.
  have hsplit : Fintype.card (Fin (2 * k + 1) × Fin (2 * k + 1)) =
      Fintype.card (Subtype (squareGrid_r2_odd.repPred k)) +
        (Fintype.card {c // ¬ squareGrid_r2_odd.repPred k c ∧
          squareGrid_r2_odd.halfTurn k c ≠ c} +
        Fintype.card {c : Fin (2 * k + 1) × Fin (2 * k + 1) //
          squareGrid_r2_odd.halfTurn k c = c}) := by
    have e : (Fin (2 * k + 1) × Fin (2 * k + 1)) ≃
        (Subtype (squareGrid_r2_odd.repPred k) ⊕
          {c // ¬ squareGrid_r2_odd.repPred k c ∧
            squareGrid_r2_odd.halfTurn k c ≠ c} ⊕
          {c : Fin (2 * k + 1) × Fin (2 * k + 1) //
            squareGrid_r2_odd.halfTurn k c = c}) :=
      { toFun := fun c => if h : squareGrid_r2_odd.repPred k c then Sum.inl ⟨c, h⟩
          else if hfix : squareGrid_r2_odd.halfTurn k c = c then
            Sum.inr (Sum.inr ⟨c, hfix⟩)
          else Sum.inr (Sum.inl ⟨c, ⟨h, hfix⟩⟩)
        invFun := fun s => match s with
          | Sum.inl a => a.1
          | Sum.inr (Sum.inl b) => b.1
          | Sum.inr (Sum.inr s) => s.1
        left_inv := fun c => by
          by_cases hp : squareGrid_r2_odd.repPred k c
          · simp [hp]
          · by_cases hfix : squareGrid_r2_odd.halfTurn k c = c
            · simp [hp, hfix]
            · simp [hp, hfix]
        right_inv := fun s => by
          cases s with
          | inl a => simp [a.2]
          | inr s => cases s with
            | inl b => simp [b.2.1, b.2.2]
            | inr s =>
              simp [squareGrid_r2_odd.repPred_of_fixed k s.2, s.2] }
    have h := Fintype.card_congr e
    rw [Fintype.card_sum, Fintype.card_sum] at h
    exact h
  have htotal : Fintype.card (Fin (2 * k + 1) × Fin (2 * k + 1)) = (2 * k + 1) ^ 2 := by
    simp [Fintype.card_prod, pow_two]
  have hA : Fintype.card (Subtype (squareGrid_r2_odd.repPred k)) =
      ((2 * k + 1) ^ 2 - 1) / 2 := by
    have hexp : (2 * k + 1 : ℕ) ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by ring
    omega
  calc Fintype.card {F : Fin (2 * k + 1) × Fin (2 * k + 1) → T //
        ∀ c, F (squareGrid_r2_odd.halfTurn k c) = σ (F c)}
      = Fintype.card ((Subtype (squareGrid_r2_odd.repPred k) → T) ×
          ({c : Fin (2 * k + 1) × Fin (2 * k + 1) //
              squareGrid_r2_odd.halfTurn k c = c} → {d : T // σ d = d})) :=
        Fintype.card_congr (fixedTilingsEquiv
          (squareGrid_r2_odd.halfTurn k) (squareGrid_r2_odd.halfTurn_involutive k)
          (squareGrid_r2_odd.repPred k)
          (fun c h => squareGrid_r2_odd.repPred_of_fixed k h)
          (fun c h => squareGrid_r2_odd.repPred_flip k h) σ htiles)
    _ = Fintype.card T ^ (((2 * k + 1) ^ 2 - 1) / 2) * tileFixedCount σ 1 := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, hA, hS, pow_one]
        simp [tileFixedCount, pow_one]

end MetaMathlibExt
