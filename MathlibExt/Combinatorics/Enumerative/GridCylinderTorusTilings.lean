/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Tilings of grids, cylinders, and tori

Kagey and Keehn count the tilings of the `n × m` grid, cylinder and torus by a finite set `T` of
tile designs, up to symmetry. A tiling is a map `F` from the cells to `T`. A symmetry acts on the
cells by a map `φ` and on the designs by a permutation `σ`, and it fixes `F` when
`F (φ c) = σ (F c)` for every cell `c`; Burnside's lemma turns the numbers of fixed tilings into
the number of tilings up to symmetry. This file defines the number of fixed tilings and counts
the tilings of the rectangular and square grids fixed by the identity. On the cylinder and the
rectangular torus, it sums the fixed-tiling counts over all translations.

On the `n × m` cylinder, applying the shift `x ↦ x + a` and then the reflection
`x ↦ n - 1 - x` sends the column `x` to `-1 - x - a` modulo `n`, so the columns this map fixes
are the solutions of `x = -1 - x - a` in `ZMod n`. Kagey and Keehn solve this equation according
to the parities of `n` and `a.val`; this file proves all three cases: one solution for odd `n`,
two for even `n` and odd `a.val`, and none when both are even.

## Main definitions

* `MetaMathlibExt.fixedTilingCount`: the number of maps `F : α → T` with `F (φ c) = σ (F c)`
  for every `c : α`.
* `MetaMathlibExt.torusShiftSum`: the sum of the fixed-tiling counts over all torus shifts.

## Main results

* `MetaMathlibExt.rectangularGrid_identity`: when `σ ^ 1 = 1`, all `|T| ^ (n * m)` tilings of
  the `n × m` grid are fixed by the identity map of the cells.
* `MetaMathlibExt.squareGrid_identity`: when `σ ^ 1 = 1`, all `|T| ^ (n ^ 2)` tilings of the
  `n × n` grid are fixed by the identity map of the cells.
* `MetaMathlibExt.squareGrid_r2_even` counts tilings fixed by a half-turn of an even square grid.
* `MetaMathlibExt.rectangularTorus_identity`: the double divisor sum for the identity tile action
  on the rectangular torus, grouped by the orders of the two shift coordinates.
* `MetaMathlibExt.reflection_shift_solutions_odd`: for odd `n`, the solutions of
  `x = -1 - x - a` in `ZMod n` form the singleton `{((n + 1) / 2) * (-1 - a)}`.
* `MetaMathlibExt.reflection_shift_solutions_even_odd`: for even `n` and odd `a.val`, the
  solutions of `x = -1 - x - a` in `ZMod n` are the residues of the integers
  `(-1 - a.val) / 2` and `(n - 1 - a.val) / 2`.
* `MetaMathlibExt.reflection_shift_solutions_even_even`: for even `n` and even `a.val`,
  there are no solutions.

## Implementation notes

The hypothesis `σ ^ 1 = 1` says that `σ = 1`, so the condition `F c = σ (F c)` holds for every
map `F`, and the fixed tilings are all `|T| ^ (n * m)` maps from the `n * m` cells to `T`. The
square grid is the case `m = n`, with `n * n = n ^ 2` cells, as in the paper.

The equation says `2 * x = -1 - a`. For odd `n` the division `(n + 1) / 2` is exact, and the
residue of its quotient is the inverse of `2` in `ZMod n`, since `2 * ((n + 1) / 2) = n + 1`.
Multiplying by it solves the equation, and multiplying back by `2` shows the solution is unique.

For even `n = 2 * k` and odd `a.val = 2 * j + 1`, both integer divisions are exact, with
quotients `-(j + 1)` and `k - (j + 1)`, and both residues solve the equation because
`2 * k = 0` in `ZMod n`. Conversely, a solution `x` gives `2 * y = 0` for `y = x + (j + 1)`, so
`n` divides `2 * y.val`; then `y.val < 2 * k` is a multiple of `k`, hence `y` is `0` or `k`.

## References

* Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
  Journal of Integer Sequences 27 (2024), Article 24.6.1; arXiv:2311.13072v2, Theorem 2.1.2
  (the tilings of the grid fixed by the identity), Theorem 2.2.2, Equation (7) (the tilings of
  the square grid fixed by the identity) and Lemma 3.0.1.
-/

namespace MetaMathlibExt

/-- **Cell map of the half-turn r².** For natural numbers $n$ and $m$, the half-turn $r^2$ acts
on the pairs $(x, y) \in \mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/m\mathbb{Z}$ (for $n, m \ge 1$,
the cells of the $n \times m$ grid) by $(x, y) \mapsto (-1 - x, -1 - y)$, that is,
$(x, y) \mapsto (n - 1 - x, m - 1 - y)$ with the coordinates taken modulo $n$ and $m$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting. -/
@[expose] public def cellR2 (n m : ℕ) (c : ZMod n × ZMod m) : ZMod n × ZMod m :=
  (-1 - c.1, -1 - c.2)

/-- **Number of fixed tilings.** Let $\alpha$ (the cells) and $T$ (the tile designs) be finite sets,
let $\varphi : \alpha \to \alpha$ be a map and let $\sigma$ be a permutation of $T$. The number of
tilings fixed by $(\varphi, \sigma)$ is the number of maps $F : \alpha \to T$ such that
$F(\varphi(c)) = \sigma(F(c))$ for every $c \in \alpha$.

This is the paper's fixed-point condition $F(c \cdot s) = F(c) \cdot g$, with $\varphi$ encoding
the action on cells and $\sigma$ the action on designs. No ambient group action is assumed, since
each fixed-point formula involves a single symmetry.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting. -/
@[expose] public def fixedTilingCount {α T : Type*} [Fintype α] [DecidableEq α]
    [Fintype T] [DecidableEq T] (φ : α → α) (σ : Equiv.Perm T) : ℕ :=
  Fintype.card {F : α → T // ∀ c, F (φ c) = σ (F c)}

/-- **Cylinder shift sum.** Let $T$ be a finite set of tile designs, let $n, m \ge 1$, let $g$ be
a map from the cells $\mathbb{Z}/n \times \mathbb{Z}/m$ to themselves, and let $\sigma$ be a
permutation of $T$. The cylinder shift sum of $g$ and $\sigma$ is the sum, over all shifts
$a \in \mathbb{Z}/n$, of the number of tilings $F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$
with $F(g(x + a, y)) = \sigma(F(x, y))$ for every cell $(x, y)$.

The shift is applied before $g$, following the paper's right-action convention, and $\sigma$
is the action of $g$ on tile designs.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting. -/
@[expose] public noncomputable def cylinderShiftSum {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m]
    (cellG : ZMod n × ZMod m → ZMod n × ZMod m) (σ : Equiv.Perm T) : ℕ :=
  ∑ a : ZMod n,
    fixedTilingCount (fun c => cellG (c.1 + a, c.2)) σ

/-- **Torus shift sum.** Let $n, m \ge 1$, let $T$ be a finite set of tile designs, let $g$ be a
map from $\mathbb{Z}/n \times \mathbb{Z}/m$ (the cells of the $n \times m$ torus) to itself and
let $\sigma$ be a permutation of $T$. For a shift $(a, b) \in \mathbb{Z}/n \times \mathbb{Z}/m$,
count the tilings $F \colon \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with
$F(g(x + a, y + b)) = \sigma(F(x, y))$ for every cell $(x, y)$. The torus shift sum is the sum of
these counts over all $nm$ shifts $(a, b)$.

Shifting the cell first and applying $g$ afterwards follows the right-action convention of the
source; shifts act trivially on tile designs.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting. -/
@[expose] public noncomputable def torusShiftSum {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m]
    (cellG : ZMod n × ZMod m → ZMod n × ZMod m) (σ : Equiv.Perm T) : ℕ :=
  ∑ a : ZMod n, ∑ b : ZMod m,
    fixedTilingCount (fun c => cellG (c.1 + a, c.2 + b)) σ

/-- **Rectangular-grid tilings fixed by the identity.** Let $n$ and $m$ be positive integers, let
$T$ be a finite set of tiles and let $\sigma$ be a permutation of $T$ with $\sigma^1 = 1$, that is,
the identity. Then the number of tilings $F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with
$F(c) = \sigma(F(c))$ for every cell $c$ equals $|T|^{nm}$.

The Burnside conclusion of Theorem 22 is not part of this single-element fixed-point statement.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 22. -/
public theorem rectangularGrid_identity {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 1 = 1) :
    fixedTilingCount (id : ZMod n × ZMod m → ZMod n × ZMod m) σ =
      Fintype.card T ^ (n * m) := by
  -- `σ ^ 1 = 1` says that `σ` is the identity, so every tiling satisfies the condition.
  rw [pow_one] at hσ
  subst hσ
  have hfixed : ∀ F : ZMod n × ZMod m → T, ∀ c, F (id c) = (1 : Equiv.Perm T) (F c) :=
    fun _ _ => rfl
  -- The fixed tilings are then all the maps from the `n * m` cells to `T`.
  rw [fixedTilingCount, Fintype.card_congr (Equiv.subtypeUnivEquiv hfixed), Fintype.card_fun,
    Fintype.card_prod, ZMod.card, ZMod.card]

/-- **Square-grid tilings fixed by the identity.** Let $n$ be a positive integer, let $T$ be a
finite set and let $\sigma$ be a permutation of $T$ with $\sigma^1 = 1$. Then the number of maps
$F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$ with $F(c) = \sigma(F(c))$ for every cell $c$ is
$|T|^{n^2}$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 24. -/
public theorem squareGrid_identity {T : Type*} [Fintype T] [DecidableEq T]
    (n : ℕ) [NeZero n] (σ : Equiv.Perm T) (hσ : σ ^ 1 = 1) :
    fixedTilingCount (id : ZMod n × ZMod n → ZMod n × ZMod n) σ =
      Fintype.card T ^ (n ^ 2) := by
  -- The square grid is the rectangular grid with `m = n`, which has `n * n = n ^ 2` cells.
  rw [rectangularGrid_identity n n σ hσ, sq]

namespace squareGrid_r2_even

/-- Restriction to one representative of each pair determines an equivariant tiling. -/
private def restrictEquiv {α T : Type*} (φ : α → α) (hφ : Function.Involutive φ)
    (p : α → Prop) [DecidablePred p] (hp : ∀ c, p (φ c) ↔ ¬p c)
    (σ : Equiv.Perm T) (hσ : Function.Involutive σ) :
    {F : α → T // ∀ c, F (φ c) = σ (F c)} ≃ (Subtype p → T) := by
  let extend (f : Subtype p → T) (c : α) : T :=
    if h : p c then f ⟨c, h⟩ else σ (f ⟨φ c, (hp c).2 h⟩)
  refine
    { toFun := fun F c => F.1 c
      invFun := fun f => ⟨extend f, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    by_cases h : p c <;> simp [extend, hp, h, hφ c, hσ _]
  · intro F
    apply Subtype.ext
    funext c
    by_cases h : p c
    · simp [extend, h]
    · simpa [extend, h, hφ c] using (F.2 (φ c)).symm
  · intro f
    funext c
    simp [extend, c.property]

end squareGrid_r2_even

/-- **Square-grid tilings fixed by the half-turn for even $n$.** Let $n$ be an even positive
integer, let $T$ be a finite set and let $\sigma$ be a permutation of $T$ with $\sigma^2 = 1$.
Let $r^2$ be the half-turn of the grid $(\mathbb{Z}/n\mathbb{Z})^2$ given by
$r^2(x, y) = (-1 - x, -1 - y)$. Then the number of maps $F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$
with $F(r^2(c)) = \sigma(F(c))$ for every cell $c$ is $|T|^{n^2/2}$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 24. -/
public theorem squareGrid_r2_even {T : Type*} [Fintype T] [DecidableEq T]
    (n : ℕ) [NeZero n] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1) (heven : Even n) :
    fixedTilingCount (cellR2 n n) σ = Fintype.card T ^ (n ^ 2 / 2) := by
  let φ := cellR2 n n
  have hφ : Function.Involutive φ := fun c => by simp [φ, cellR2]
  -- Reduction modulo two distinguishes one cell in each half-turn pair.
  let parity := ZMod.castHom (even_iff_two_dvd.mp heven) (ZMod 2)
  let evenColumn (c : ZMod n × ZMod n) := parity c.1 = 0
  have hflip (c) : evenColumn (φ c) ↔ ¬evenColumn c := by
    change parity (-1 - c.1) = 0 ↔ parity c.1 ≠ 0
    rw [map_sub, map_neg, map_one]
    exact (by decide : ∀ x : ZMod 2, -1 - x = 0 ↔ x ≠ 0) _
  -- The half-turn bijects the odd-column cells with the even-column cells.
  let e : {c // ¬evenColumn c} ≃ Subtype evenColumn :=
    (hφ.toPerm φ).subtypeEquiv fun c => (hflip c).symm
  have hcard : n ^ 2 - Fintype.card (Subtype evenColumn) = Fintype.card (Subtype evenColumn) := by
    simpa only [Fintype.card_subtype_compl, Fintype.card_prod, ZMod.card, sq] using
      Fintype.card_congr e
  have htiles : Function.Involutive σ := fun t => by
    simpa [sq] using DFunLike.congr_fun hσ t
  calc
    fixedTilingCount (cellR2 n n) σ = Fintype.card (Subtype evenColumn → T) :=
      Fintype.card_congr (squareGrid_r2_even.restrictEquiv φ hφ evenColumn hflip σ htiles)
    _ = _ := by rw [Fintype.card_fun, show Fintype.card (Subtype evenColumn) = n ^ 2 / 2 by omega]

namespace rectangularTorus_identity

/-- A tiling fixed by translation by `v` is a choice of tile for each coset of its multiples. -/
private theorem fixedTilingCount_add {G T : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [Fintype T] [DecidableEq T] (v : G) :
    fixedTilingCount (· + v) (1 : Equiv.Perm T) =
      Fintype.card T ^ (Fintype.card G / addOrderOf v) := by
  classical
  let Q := G ⧸ AddSubgroup.zmultiples v
  have hv : (v : Q) = 0 := (QuotientAddGroup.eq_zero_iff v).2 (AddSubgroup.mem_zmultiples v)
  let e : {F : G → T // Function.Periodic F v} ≃ (Q → T) :=
    { toFun := fun F => F.2.lift
      invFun := fun f => ⟨fun x => f (x : Q), fun x => by
        change f ((x + v : G) : Q) = f (x : Q)
        rw [QuotientAddGroup.mk_add, hv, add_zero]⟩
      left_inv := fun _ => rfl
      right_inv := fun f => funext fun q => QuotientAddGroup.induction_on q fun _ => rfl }
  have hcard : Fintype.card Q = Fintype.card G / addOrderOf v := by
    rw [← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, AddSubgroup.index_eq_card_sub,
      Nat.card_zmultiples, Nat.card_eq_fintype_card]
  calc
    fixedTilingCount (· + v) (1 : Equiv.Perm T) = Fintype.card (Q → T) :=
      Fintype.card_congr e
    _ = _ := by rw [Fintype.card_fun, hcard]

/-- Group shifts in a cyclic coordinate by their additive orders. -/
private theorem sum_by_order (n : ℕ) [NeZero n] (f : ℕ → ℕ) :
    ∑ a : ZMod n, f (addOrderOf a) = ∑ d ∈ n.divisors, Nat.totient d * f d := by
  classical
  have hmem (a : ZMod n) : addOrderOf a ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨by simpa using (addOrderOf_dvd_card (x := a)), NeZero.ne n⟩
  rw [← Finset.sum_fiberwise_of_maps_to' (fun a _ => hmem a) f]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_const, smul_eq_mul, IsAddCyclic.card_addOrderOf_eq_totient]
  simpa using (Nat.mem_divisors.mp hd).1

end rectangularTorus_identity

/-- **Cylinder fixed-tiling count for the identity.** Let $T$ be a finite set of tile designs,
let $n, m \ge 1$, and let $\sigma$ be a permutation of $T$ with $\sigma^1 = 1$, that is, the
identity. Then the cylinder shift sum of the identity map of $\mathbb{Z}/n \times \mathbb{Z}/m$
and $\sigma$ equals $\sum_{d \mid n} \varphi(d)\, |T|^{nm/d}$, where $d$ runs over the positive
divisors of $n$ and $\varphi$ is Euler's totient function.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 28. -/
public theorem cylinder_identity {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 1 = 1) :
    cylinderShiftSum n m id σ =
      ∑ d ∈ n.divisors, Nat.totient d * Fintype.card T ^ (n * m / d) := by
  rw [pow_one] at hσ
  subst σ
  calc
    cylinderShiftSum n m id (1 : Equiv.Perm T) =
        ∑ a : ZMod n, Fintype.card T ^ (n * m / addOrderOf a) := by
      rw [cylinderShiftSum]
      refine Finset.sum_congr rfl fun a _ => ?_
      -- The vertical coordinate is fixed, so the translation has the order of `a`.
      have hshift : (fun c : ZMod n × ZMod m => id (c.1 + a, c.2)) = (· + (a, 0)) := by
        funext c
        rcases c with ⟨x, y⟩
        simp only [id_eq, Prod.mk_add_mk, add_zero]
      rw [hshift, rectangularTorus_identity.fixedTilingCount_add, Fintype.card_prod, ZMod.card,
        ZMod.card, Prod.addOrderOf_mk, addOrderOf_zero, Nat.lcm_one_right]
    _ = _ := rectangularTorus_identity.sum_by_order n (fun d => Fintype.card T ^ (n * m / d))

/-- **Torus fixed-tiling sum for the identity.** Let $n$ and $m$ be positive integers, let $T$ be
a finite set of tiles and let $\sigma$ be a permutation of $T$ with $\sigma^1 = 1$, that is, the
identity. For $(a, b) \in \mathbb{Z}/n \times \mathbb{Z}/m$ let $N(a, b)$ be the number of tilings
$F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with $F(x + a, y + b) = \sigma(F(x, y))$ for every
cell $(x, y)$. Then, with $\varphi$ Euler's totient function,
$$\sum_{a \in \mathbb{Z}/n} \sum_{b \in \mathbb{Z}/m} N(a, b) =
\sum_{c \mid m} \sum_{d \mid n} \varphi(c) \, \varphi(d) \, |T|^{mn / \operatorname{lcm}(c, d)}.$$

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 34. -/
public theorem rectangularTorus_identity {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 1 = 1) :
    torusShiftSum n m id σ =
      ∑ c ∈ m.divisors, ∑ d ∈ n.divisors,
        Nat.totient c * Nat.totient d *
          Fintype.card T ^ (m * n / Nat.lcm c d) := by
  rw [pow_one] at hσ
  subst σ
  let count (c d : ℕ) := Fintype.card T ^ (m * n / Nat.lcm c d)
  calc
    torusShiftSum n m id (1 : Equiv.Perm T) =
        ∑ b : ZMod m, ∑ a : ZMod n, count (addOrderOf b) (addOrderOf a) := by
      rw [torusShiftSum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      change fixedTilingCount (· + (a, b)) (1 : Equiv.Perm T) = _
      rw [rectangularTorus_identity.fixedTilingCount_add, Fintype.card_prod, ZMod.card, ZMod.card,
        Prod.addOrderOf_mk, Nat.mul_comm n m, Nat.lcm_comm]
    _ = ∑ c ∈ m.divisors, c.totient * (∑ d ∈ n.divisors, d.totient * count c d) := by
      simp_rw [rectangularTorus_identity.sum_by_order n (count _)]
      exact rectangularTorus_identity.sum_by_order m
        (fun c => ∑ d ∈ n.divisors, d.totient * count c d)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc, count]

/-- **Square-torus fixed points of the identity.** Let $n$ be a positive integer, let $T$ be a
finite set of tile designs, and let $\sigma$ be the identity permutation of $T$. Let $S$ be the
sum, over all shifts $v \in (\mathbb{Z}/n\mathbb{Z})^2$, of the number of tilings
$F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$ with $F(c + v) = \sigma(F(c))$ for every cell $c$. Then
$S = \sum_{d_1 \mid n} \sum_{d_2 \mid n} \varphi(d_1) \, \varphi(d_2) \,
|T|^{n^2/\operatorname{lcm}(d_1, d_2)}$, where $d_1$ and $d_2$ run over the positive divisors of
$n$ and $\varphi$ is Euler's totient function.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 38. -/
public theorem squareTorus_identity {T : Type*} [Fintype T] [DecidableEq T]
    (n : ℕ) [NeZero n] (σ : Equiv.Perm T) (hσ : σ ^ 1 = 1) :
    torusShiftSum n n id σ =
      ∑ d₁ ∈ n.divisors, ∑ d₂ ∈ n.divisors,
        Nat.totient d₁ * Nat.totient d₂ *
          Fintype.card T ^ (n ^ 2 / Nat.lcm d₁ d₂) := by
  simpa only [pow_two] using rectangularTorus_identity n n σ hσ

/-- **Solution of $x = -1-x-a$ modulo odd $n$.** Let $n$ be a positive odd integer and
$a \in \mathbb{Z}/n$. Then the set of $x \in \mathbb{Z}/n$ with $x = -1-x-a$ is the singleton
$\{k(-1-a)\}$, where $k$ is the residue mod $n$ of the integer $(n+1)/2$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Lemma 25. -/
public theorem reflection_shift_solutions_odd (n : ℕ) [NeZero n]
    (a : ZMod n) (hn : Odd n) :
    {x : ZMod n | x = -1 - x - a} =
      {(((n + 1) / 2 : ℕ) : ZMod n) * (-1 - a)} := by
  -- The residue of `(n + 1) / 2` is the inverse of `2`: twice it is `n + 1 = 1` in `ZMod n`.
  have hinv : (((n + 1) / 2 : ℕ) : ZMod n) * 2 = 1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod n)
      (Nat.div_mul_cancel (even_iff_two_dvd.mp hn.add_one))
    push_cast at h
    simpa using h
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    linear_combination (((n + 1) / 2 : ℕ) : ZMod n) * hx - x * hinv
  · rintro rfl
    linear_combination (-1 - a) * hinv

/-- **Solutions of $x = -1-x-a$ modulo even $n$ for odd $a$.** Let $n$ be a positive even
integer and $a \in \mathbb{Z}/n$ whose representative $\bar a \in \{0, \dots, n-1\}$ is odd.
Then the set of $x \in \mathbb{Z}/n$ with $x = -1-x-a$ consists of the residues mod $n$ of the
integers $(-1-\bar a)/2$ and $(n-1-\bar a)/2$.

The divisions by $2$ are exact divisions of integers, carried out before reducing mod $n$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Lemma 25. -/
public theorem reflection_shift_solutions_even_odd (n : ℕ) [NeZero n]
    (a : ZMod n) (hn : Even n) (ha : Odd a.val) :
    {x : ZMod n | x = -1 - x - a} =
      {((((-1 : ℤ) - a.val) / 2 : ℤ) : ZMod n),
        ((((n : ℤ) - 1 - a.val) / 2 : ℤ) : ZMod n)} := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨j, hj⟩ := ha
  -- Both divisions are exact, with quotients `-(j + 1)` and `k - (j + 1)`.
  have h₁ : ((-1 : ℤ) - a.val) / 2 = -(j + 1) := by
    rw [hj]
    push_cast
    omega
  have h₂ : ((n : ℤ) - 1 - a.val) / 2 = k - (j + 1) := by
    rw [hj, hk]
    push_cast
    omega
  -- In `ZMod n`, `a = 2 * j + 1` and `2 * k = n = 0`.
  have ha' : a = 2 * j + 1 := by
    rw [← ZMod.natCast_zmod_val a, hj]
    push_cast
    ring
  have hk' : (2 * k : ZMod n) = 0 := by
    rw [← ZMod.natCast_self n, hk]
    push_cast
    ring
  rw [h₁, h₂]
  push_cast
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    -- `y = x + (j + 1)` satisfies `2 * y = 0`, so `n = 2 * k` divides `2 * y.val`. Hence
    -- `y.val < 2 * k` is a multiple of `k`, that is `0` or `k`.
    set y : ZMod n := x + (j + 1) with hy
    have h2y : 2 * y = 0 := by linear_combination hx - ha'
    have hdvd : n ∣ 2 * y.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact h2y
    have hlt := ZMod.val_lt y
    have hyv : y = (y.val : ZMod n) := (ZMod.natCast_zmod_val y).symm
    generalize y.val = v at hdvd hlt hyv
    subst hk
    obtain ⟨c, rfl⟩ : k ∣ v := by
      rw [← two_mul] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
    have hc : c < 2 := Nat.lt_of_mul_lt_mul_left (a := k) (by omega)
    interval_cases c <;> push_cast at hyv
    · exact Or.inl (by linear_combination hy.symm.trans hyv)
    · exact Or.inr (by linear_combination hy.symm.trans hyv)
  · rintro (rfl | rfl)
    · linear_combination ha'
    · linear_combination ha' + hk'

/-- **No solutions of $x = -1-x-a$ modulo $n$ when $n$ and $a$ are even.** Let $n$ be a
positive even integer and $a \in \mathbb{Z}/n$ whose representative in $\{0, \dots, n-1\}$ is
even. Then no $x \in \mathbb{Z}/n$ satisfies $x = -1-x-a$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Lemma 25. -/
public theorem reflection_shift_solutions_even_even (n : ℕ) [NeZero n]
    (a : ZMod n) (hn : Even n) (ha : Even a.val) :
    {x : ZMod n | x = -1 - x - a} = ∅ := by
  let f : ZMod n →+* ZMod 2 := ZMod.castHom (even_iff_two_dvd.mp hn) (ZMod 2)
  have htwo : (2 : ZMod 2) = 0 := by decide
  have ha₀ : f a = 0 := by
    change ZMod.cast a = (0 : ZMod 2)
    rw [← ZMod.natCast_val]
    exact ha.natCast_zmod_two
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  change x = -1 - x - a at hx
  have h : 2 * x = -1 - a := by
    rwa [two_mul, ← eq_sub_iff_add_eq, sub_right_comm]
  have hzero : (0 : ZMod 2) = 1 := by
    have hneg : (-1 : ZMod 2) = 1 := by decide
    simpa only [map_mul, map_ofNat, map_sub, map_neg, map_one, htwo, ha₀, zero_mul,
      sub_zero, hneg] using congrArg f h
  exact zero_ne_one hzero

end MetaMathlibExt
