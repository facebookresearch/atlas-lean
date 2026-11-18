/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.CommunicationComplexity.Deterministic

/-!
# Public-coin randomized communication protocols

A public-coin protocol is a family of deterministic protocols indexed by a shared random string
`r` drawn uniformly from a finite set `R` (A. Rao and A. Yehudayoff, *Communication Complexity*,
early draft, Chapter 3, "Variants of Randomized Protocols"). Its cost is the largest depth of a
member, and its error on an input pair is the fraction of random strings on which the output is
wrong.

The main result is the random-hash protocol for equality (Rao and Yehudayoff, Figure 3.1):
Alice and Bob share a uniformly random function `h : {0,1}^n → {0,1}^k`, Alice sends `h x`
and Bob announces whether it equals `h y`. It costs `k + 1` bits, never errs when `x = y`, and
errs with probability exactly `2 ^ (-k)` when `x ≠ y`, whereas every deterministic protocol
for equality of `n ≥ 1` bits needs `n + 1` bits (`commComplexity_eqFn`).
-/

@[expose] public section

namespace MathlibExt.Computability.CommunicationComplexity

/-- **Public-coin randomized protocol.** A family `run r` of deterministic protocols indexed by
the shared random string `r : R`; the string is drawn uniformly from the finite set `R`,
independently of the inputs (A. Rao and A. Yehudayoff, *Communication Complexity*, early draft,
Chapter 3). -/
structure PublicCoinProtocol (X Y R : Type*) where
  /-- The deterministic protocol run when the shared random string is `r`. -/
  run : R → Protocol X Y

namespace PublicCoinProtocol

variable {X Y R : Type*} [Fintype R]

/-- **Cost of a public-coin protocol.** The largest depth of the deterministic protocols it
runs, over all random strings. -/
def cost (P : PublicCoinProtocol X Y R) : ℕ :=
  Finset.univ.sup fun r => (P.run r).depth

/-- **Error probability of a public-coin protocol.** For `f : X → Y → Bool` and an input pair
`(x, y)`, the fraction of random strings `r : R` on which `run r` outputs a value other than
`f x y`. -/
noncomputable def errorProb (P : PublicCoinProtocol X Y R) (f : X → Y → Bool) (x : X) (y : Y) :
    ℚ :=
  ((Finset.univ.filter fun r => (P.run r).eval x y ≠ f x y).card : ℚ) / Fintype.card R

/-- **Each run costs at most the cost.** Every deterministic protocol run by a public-coin
protocol has depth at most its cost. -/
theorem depth_le_cost (P : PublicCoinProtocol X Y R) (r : R) : (P.run r).depth ≤ P.cost :=
  Finset.le_sup (f := fun r => (P.run r).depth) (Finset.mem_univ r)

end PublicCoinProtocol

/-- **Collision count of a uniformly random function.** For distinct points `a ≠ b` of a finite
type, exactly a `1 / |β|` fraction of the functions `h : α → β` satisfy `h a = h b`:
`|{h | h a = h b}| · |β| = |α → β|`. -/
theorem card_filter_apply_eq_apply_mul {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {a b : α} (hab : a ≠ b) :
    (Finset.univ.filter fun h : α → β => h a = h b).card * Fintype.card β =
      Fintype.card (α → β) := by
  let e : (α → β) ≃ {h : α → β // h a = h b} × β :=
    { toFun := fun h => (⟨Function.update h a (h b), by simp [Function.update_of_ne hab.symm]⟩,
        h a)
      invFun := fun p => Function.update p.1.1 a p.2
      left_inv := fun h => by simp
      right_inv := fun p => by
        obtain ⟨⟨g, hg⟩, c⟩ := p
        ext x
        · by_cases hx : x = a
          · subst hx; simp [Function.update_of_ne hab.symm, hg]
          · simp [Function.update_of_ne hx]
        · simp }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_subtype]

/-- **Random-hash protocol for equality.** With shared random function
`h : {0,1}^n → {0,1}^k`, Alice sends the `k` bits of `h x` and Bob announces whether they equal
`h y` (A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 3, Figure 3.1).
-/
def eqHashProtocol (n k : ℕ) :
    PublicCoinProtocol (Fin n → Bool) (Fin n → Bool) ((Fin n → Bool) → Fin k → Bool) where
  run h := Protocol.aliceSends k h fun m =>
    Protocol.bob (fun y => decide (m = h y)) (.output false) (.output true)

/-- **Output of the random-hash protocol.** With shared random function `h`, the protocol
outputs `true` exactly when `h x = h y`. -/
theorem eval_eqHashProtocol {n k : ℕ} (h : (Fin n → Bool) → Fin k → Bool)
    (x y : Fin n → Bool) : ((eqHashProtocol n k).run h).eval x y = decide (h x = h y) := by
  simp only [eqHashProtocol, Protocol.eval_aliceSends]
  by_cases hxy : h x = h y <;> simp [Protocol.eval, hxy]

/-- **Cost of the random-hash protocol.** The random-hash protocol for equality costs at most
`k + 1` bits. -/
theorem cost_eqHashProtocol_le (n k : ℕ) : (eqHashProtocol n k).cost ≤ k + 1 :=
  Finset.sup_le fun _ _ =>
    Protocol.depth_aliceSends_le _ _ _ fun _ => by simp [Protocol.depth]

/-- **No error on equal inputs.** The random-hash protocol never errs when `x = y`. -/
theorem errorProb_eqHashProtocol_self {n k : ℕ} (x : Fin n → Bool) :
    (eqHashProtocol n k).errorProb (eqFn n) x x = 0 := by
  simp [PublicCoinProtocol.errorProb, eval_eqHashProtocol, eqFn]

/-- **Error of the random-hash protocol for equality.** On distinct inputs the random-hash
protocol errs with probability exactly `1 / 2 ^ k`: it errs exactly when the random function
collides on `x` and `y` (A. Rao and A. Yehudayoff, *Communication Complexity*, early draft,
Chapter 3: "if `x ≠ y`, the probability that `h(x) = h(y)` is at most `2^-k`"). -/
theorem errorProb_eqHashProtocol_of_ne {n k : ℕ} {x y : Fin n → Bool} (hxy : x ≠ y) :
    (eqHashProtocol n k).errorProb (eqFn n) x y = 1 / 2 ^ k := by
  have hset : (Finset.univ.filter fun h : (Fin n → Bool) → Fin k → Bool =>
      ((eqHashProtocol n k).run h).eval x y ≠ eqFn n x y) =
      Finset.univ.filter fun h => h x = h y := by
    ext h
    simp [eval_eqHashProtocol, eqFn, hxy]
  have hcard := card_filter_apply_eq_apply_mul (β := Fin k → Bool) hxy
  have hB : Fintype.card (Fin k → Bool) = 2 ^ k := by simp
  have hpos : (0 : ℚ) < 2 ^ k := by positivity
  rw [PublicCoinProtocol.errorProb, hset, ← hcard, hB]
  push_cast
  field_simp
  have : ((Finset.univ.filter fun h : (Fin n → Bool) → Fin k → Bool => h x = h y).card : ℚ) ≠
      0 := by
    have h0 : 0 < (Finset.univ.filter fun h : (Fin n → Bool) → Fin k → Bool =>
        h x = h y).card := Finset.card_pos.2 ⟨fun _ => fun _ => false, by simp⟩
    exact_mod_cast h0.ne'
  field_simp

end MathlibExt.Computability.CommunicationComplexity
