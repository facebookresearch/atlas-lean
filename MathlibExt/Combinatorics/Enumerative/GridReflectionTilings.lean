/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GridCylinderTorusTilings
public import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Reflection-fixed tilings of a rectangular grid

`rectangularGrid_f_even` counts fixed tilings by choosing one tile per reflected pair of cells.
For odd width, `rectangularGrid_f_odd` also counts the reflection-invariant tiles on the axis.

## References

Peter Kagey and William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
Journal of Integer Sequences 27 (2024), Article 24.6.1, pp. 13–15, Theorems 22 and 24.
The rectangular reflection counts are equation (4) of Theorem 22. The proof of `squareGrid_f_odd`
follows the paper's derivation of equation (9) in Theorem 24 by setting `m = n` in Theorem 22.
-/

namespace MetaMathlibExt

/-- **Cell map of the reflection f.** For natural numbers $n$ and $m$, the reflection $f$ acts on
the pairs $(x, y) \in \mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/m\mathbb{Z}$ (for $n, m \ge 1$, the
cells of the $n \times m$ grid) by $(x, y) \mapsto (-1 - x, y)$, that is,
$(x, y) \mapsto (n - 1 - x, y)$ with the first coordinate taken modulo $n$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting. -/
@[expose] public def cellF (n m : ℕ) (c : ZMod n × ZMod m) : ZMod n × ZMod m :=
  (-1 - c.1, c.2)

/-- **Tile designs fixed by a power of a permutation.** For a finite set $T$ of tile designs, a
permutation $\sigma$ of $T$ and a natural number $k$, this is the number of designs $d \in T$ with
$\sigma^k(d) = d$.

When $\sigma$ is the action of a symmetry $g$ on tile designs, this is the paper's $t_{g^k}$; for
$k = 0$ it is $t_{\mathrm{id}} = |T|$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting. -/
@[expose] public def tileFixedCount {T : Type*} [Fintype T] [DecidableEq T]
    (σ : Equiv.Perm T) (k : ℕ) : ℕ :=
  Fintype.card {d : T // (σ ^ k) d = d}

namespace rectangularGrid_f_even

/-- Restriction to the left half, extended to the right half by reflection. -/
private def restrictEquiv {R T : Type*} (k : ℕ) (σ : Equiv.Perm T) (hσ : Function.Involutive σ) :
    {F : Fin (k + k) × R → T // ∀ c, F (c.1.rev, c.2) = σ (F c)} ≃ (Fin k × R → T) := by
  have append_right (a b : Fin k → T) (i : Fin k) : Fin.append a b (i.addNat k) = b i := by
    rw [← Fin.natAdd_eq_addNat, Fin.append_right]
  let extend (f : Fin k × R → T) (c : Fin (k + k) × R) :=
    Fin.append (fun i => f (i, c.2)) (fun i => σ (f (i.rev, c.2))) c.1
  refine
    { toFun := fun F (i, y) => F.val (i.castAdd k, y)
      invFun := fun f => ⟨extend f, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨x, y⟩
    induction x using Fin.addCases <;>
      simp [extend, Fin.rev_castAdd, Fin.rev_addNat, append_right, hσ _]
  · intro F
    apply Subtype.ext
    funext ⟨x, y⟩
    induction x using Fin.addCases with
    | left i => simp [extend]
    | right i =>
      simpa [extend, Fin.rev_castAdd, append_right] using (F.property (i.rev.castAdd k, y)).symm
  · intro f
    funext ⟨i, y⟩
    simp [extend]

end rectangularGrid_f_even

/-- **Rectangular-grid tilings fixed by the reflection $f$, $n$ even.** Let $n$ and $m$ be
positive integers with $n$ even, let $T$ be a finite set of tiles and let $\sigma$ be a
permutation of $T$ with $\sigma^2 = 1$. Let $f$ be the reflection of
$\mathbb{Z}/n \times \mathbb{Z}/m$ given by $f(x, y) = (-1 - x, y)$. Then the number of tilings
$F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with $F(f(c)) = \sigma(F(c))$ for every cell $c$
equals $|T|^{nm/2}$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 22. -/
public theorem rectangularGrid_f_even {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1)
    (heven : Even n) :
    fixedTilingCount (cellF n m) σ = Fintype.card T ^ (n * m / 2) := by
  have htiles : Function.Involutive σ := fun t => by
    simpa [sq] using DFunLike.congr_fun hσ t
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have hrev (x : Fin n.succ) : -1 - x = x.rev := by
    rw [← Fin.last_sub, show (-1 : Fin n.succ) = Fin.last n from Fin.ext Fin.coe_neg_one]
  change Fintype.card {F : Fin n.succ × ZMod m → T //
    ∀ c, F (-1 - c.1, c.2) = σ (F c)} = _
  simp_rw [hrev]
  obtain ⟨k, hk⟩ := heven
  rw [hk, Fintype.card_congr (rectangularGrid_f_even.restrictEquiv k σ htiles),
    Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, ZMod.card, ← two_mul,
    Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

namespace rectangularGrid_f_odd

/-- Restriction to the left half and the middle column, with reflection as its inverse. -/
private def restrictEquiv {R T : Type*} (k : ℕ) (σ : Equiv.Perm T) (hσ : Function.Involutive σ) :
    {F : Fin (2 * k + 1) × R → T // ∀ c, F (-1 - c.1, c.2) = σ (F c)} ≃
      ((Fin k × R → T) × (R → {d : T // σ d = d})) := by
  have hrev (x : Fin (2 * k + 1)) : -1 - x = x.rev := by
    rw [← Fin.last_sub, show (-1 : Fin (2 * k + 1)) = Fin.last (2 * k) from
      Fin.ext (Fin.coe_neg_one)]
  simp only [Prod.forall, hrev]
  let left (i : Fin k) : Fin (2 * k + 1) := ⟨i.val, by omega⟩
  let mid : Fin (2 * k + 1) := ⟨k, by omega⟩
  have hmid : mid.rev = mid := Fin.ext (by dsimp [Fin.rev, mid]; omega)
  have rev_lt (x : Fin (2 * k + 1)) (h : k < x.val) : x.rev.val < k := by
    rw [Fin.val_rev]
    omega
  have rev_gt (x : Fin (2 * k + 1)) (h : x.val < k) : k < x.rev.val := by
    rw [Fin.val_rev]
    omega
  let extend (f : Fin k × R → T) (d : R → {t : T // σ t = t}) (x : Fin (2 * k + 1)) (y : R) :=
    if hl : x.val < k then f (⟨x.val, hl⟩, y)
    else if hm : x.val = k then (d y).val
    else σ (f (⟨x.rev.val, rev_lt x (by omega)⟩, y))
  refine
    { toFun := fun F => (fun (i, y) => F.val (left i, y),
        fun y => ⟨F.val (mid, y), by simpa [hmid] using (F.property mid y).symm⟩)
      invFun := fun (f, d) => ⟨fun (x, y) => extend f d x y, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x y
    rcases lt_trichotomy x.val k with h | h | h
    · simp [-Fin.val_rev, extend, h, not_lt_of_gt (rev_gt x h), (rev_gt x h).ne']
    · have hx : x = mid := Fin.ext h
      subst x
      simp [hmid, extend, mid, (d y).property]
    · simp [-Fin.val_rev, extend, not_lt_of_gt h, h.ne', rev_lt x h, hσ _]
  · intro F
    apply Subtype.ext
    funext ⟨x, y⟩
    rcases lt_trichotomy x.val k with h | h | h
    · simp [extend, h, left]
    · have hx : x = mid := Fin.ext h
      subst x
      simp [extend, mid]
    · simpa [-Fin.val_rev, extend, not_lt_of_gt h, h.ne', left] using (F.property x.rev y).symm
  · rintro ⟨f, d⟩
    apply Prod.ext
    · funext ⟨i, y⟩
      simp [extend, left, i.isLt]
    · funext y
      exact Subtype.ext (by simp [extend, mid])

end rectangularGrid_f_odd

/-- **Rectangular-grid tilings fixed by the reflection $f$, $n$ odd.** Let $n$ and $m$ be positive
integers with $n$ odd, let $T$ be a finite set of tiles, let $\sigma$ be a permutation of $T$ with
$\sigma^2 = 1$, and let $t$ be the number of tiles $d \in T$ with $\sigma(d) = d$. Let $f$ be the
reflection of $\mathbb{Z}/n \times \mathbb{Z}/m$ given by $f(x, y) = (-1 - x, y)$. Then the number
of tilings $F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with $F(f(c)) = \sigma(F(c))$ for every
cell $c$ equals $|T|^{m(n-1)/2} \, t^m$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 22. -/
public theorem rectangularGrid_f_odd {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1)
    (hodd : Odd n) :
    fixedTilingCount (cellF n m) σ =
      Fintype.card T ^ (m * (n - 1) / 2) * tileFixedCount σ 1 ^ m := by
  obtain ⟨k, rfl⟩ := hodd
  have htiles : Function.Involutive σ := fun t => by
    simpa [sq] using DFunLike.congr_fun hσ t
  calc
    _ = Fintype.card ((Fin k × ZMod m → T) × (ZMod m → {d : T // σ d = d})) :=
      Fintype.card_congr (rectangularGrid_f_odd.restrictEquiv k σ htiles)
    _ = _ := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_prod,
        Fintype.card_fin, ZMod.card, Nat.add_sub_cancel, Nat.mul_left_comm m 2 k,
        Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_comm m k]
      simp [tileFixedCount]

/-- **Square-grid tilings fixed by the reflection $f$ for odd $n$.** Let $n$ be an odd positive
integer, let $T$ be a finite set, let $\sigma$ be a permutation of $T$ with $\sigma^2 = 1$, and
write $t_\sigma$ for the number of elements $t \in T$ with $\sigma(t) = t$. Let $f$ be the
reflection of the grid $(\mathbb{Z}/n\mathbb{Z})^2$ given by $f(x, y) = (-1 - x, y)$. Then the
number of maps $F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$ with $F(f(c)) = \sigma(F(c))$ for every
cell $c$ is $|T|^{(n^2 - n)/2} \cdot t_\sigma^{\,n}$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 24. -/
public theorem squareGrid_f_odd {T : Type*} [Fintype T] [DecidableEq T]
    (n : ℕ) [NeZero n] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1) (hodd : Odd n) :
    fixedTilingCount (cellF n n) σ =
      Fintype.card T ^ ((n ^ 2 - n) / 2) * tileFixedCount σ 1 ^ n := by
  have hnum : n * (n - 1) = n ^ 2 - n := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_two]
  rw [rectangularGrid_f_odd n n σ hσ hodd, hnum]

end MetaMathlibExt
