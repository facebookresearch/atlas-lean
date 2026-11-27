/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.Abel

/-!
# Perfect centreless groups and the largest conjugacy class (Kourovka Notebook Problem 20.30)

Kourovka Notebook, Problem 20.30 (P. M. Neumann and M. R. Vaughan-Lee; I. B. Gorshkov), marked
solved in the 21st issue: let `G` be a perfect and centreless finite group, and let `n` be the
maximum size of a conjugacy class in `G`. Is it true that `|G| ≤ n²`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.30 (P. M. Neumann and M. R. Vaughan-Lee;
I. B. Gorshkov). UnsolvedMath record UM-00701688 (`KOU-20.30`), dataset ulamai/UnsolvedMath v1.8.0.

Perfect is Mathlib's `Group.IsPerfect G` (`commutator G = ⊤`), centreless is `Subgroup.center G =
⊥`; the class of `x` is `conjugatesOf x`. Since `n = |x^G|` for some `x`, the inequality `|G| ≤ n²`
is stated as `|G| ≤ |x^G|²` for some `x ∈ G`.

A block upper triangular group over the field of five elements refutes the proposed bound.
Its block sizes are 32, 2, 32 and 2. The (1,3) block alone contributes 1024 independent entries,
whereas a conjugate of any fixed element can be encoded by 396 field entries.
-/

namespace MathlibExt.GroupTheory.PerfectCentrelessOrderMaxClassKourovka20Problem30Wanted

/-- **Kourovka 20.30: the order of a perfect centreless group and its largest conjugacy class.**
The proposition that every finite group $G$ that is perfect ($[G, G] = G$) and has trivial centre
contains an element $x$ with $|G| \le |x^G|^2$, where $x^G$ is the conjugacy class of $x$.
Equivalently, $|G| \le n^2$, where $n$ is the largest size of a conjugacy class of $G$. -/
@[expose] public def perfectCentrelessOrderLeMaxClassSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsPerfect G → Subgroup.center G = ⊥ →
    ∃ x : G, Nat.card G ≤ (conjugatesOf x).ncard ^ 2

open Matrix
open scoped MatrixGroups commutatorElement

private abbrev F := ZMod 5
private abbrev I := Fin 32
private abbrev J := Fin 2
private abbrev M (m n : Type) := Matrix m n F
private abbrev S := SL(2, F)

-- Store the diagonal and strict upper blocks of the matrix
-- ⎛1  a  c  f⎞
-- ⎜0  s  b  e⎟
-- ⎜0  0  1  d⎟
-- ⎝0  0  0  t⎠.
@[ext] private structure Blocks where
  s : S
  t : S
  a : M I J
  b : M J I
  c : M I I
  d : M I J
  e : M J J
  f : M I J

private instance blocksFinite : Finite Blocks :=
  Finite.of_injective (fun x : Blocks ↦ (x.s, x.t, x.a, x.b, x.c, x.d, x.e, x.f)) (by
    intro x y h
    simpa [Blocks.ext_iff] using h)

private def identity : Blocks := ⟨1, 1, 0, 0, 0, 0, 0, 0⟩
private instance blocksOne : One Blocks := ⟨identity⟩
private def product (x y : Blocks) : Blocks :=
  ⟨x.s * y.s, x.t * y.t, y.a + x.a * y.s.val, x.s.val * y.b + x.b,
    y.c + x.a * y.b + x.c, y.d + x.d * y.t.val,
    x.s.val * y.e + x.b * y.d + x.e * y.t.val, y.f + x.a * y.e + x.c * y.d + x.f * y.t.val⟩

private instance blocksMul : Mul Blocks := ⟨product⟩

private def inverse (x : Blocks) : Blocks :=
  let a := -x.a * x.s⁻¹.val
  let b := -x.s⁻¹.val * x.b
  let c := -(x.c + a * x.b)
  ⟨x.s⁻¹, x.t⁻¹, a, b, c, -x.d * x.t⁻¹.val,
    -(x.s⁻¹.val * x.e + b * x.d) * x.t⁻¹.val, -(x.f + a * x.e + c * x.d) * x.t⁻¹.val⟩

private instance blocksInv : Inv Blocks := ⟨inverse⟩

private theorem val_inv_mul (s : S) : s⁻¹.val * s.val = 1 :=
  congrArg Subtype.val (inv_mul_cancel s)

private instance blocksGroup : Group Blocks := Group.ofLeftAxioms
  (by
    intro x y z
    change product (product x y) z = product x (product y z)
    apply Blocks.ext <;>
      simp only [product, SpecialLinearGroup.coe_mul, Matrix.mul_assoc, Matrix.mul_add,
        Matrix.add_mul, mul_assoc] <;> abel)
  (by
    intro x
    change product identity x = x
    apply Blocks.ext <;> simp [product, identity])
  (by
    intro x
    change product (inverse x) x = identity
    apply Blocks.ext <;>
      simp only [product, inverse, identity, Matrix.mul_assoc, Matrix.neg_mul, val_inv_mul,
        Matrix.mul_one, inv_mul_cancel, add_neg_cancel])

private def diagonalBlocks (s t : S) : Blocks := { identity with s, t }
private def shear12 (a : M I J) : Blocks := { identity with a }
private def shear23 (b : M J I) : Blocks := { identity with b }
private def shear13 (c : M I I) : Blocks := { identity with c }
private def lastColumn (d : M I J) (e : M J J) (f : M I J) : Blocks := { identity with d, e, f }

private theorem block_mul (x y : Blocks) : x * y = product x y := rfl
private theorem block_one : (1 : Blocks) = identity := rfl

private theorem mem_derived_of_mul {x y z : Blocks} (h : x * y = z * (y * x)) :
    z ∈ commutator Blocks := by
  have he : ⁅x, y⁆ = z := by simp [commutatorElement_def, h, mul_assoc]
  exact he ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

-- The two diagonal copies of SL₂ are perfect.
private theorem diagonal_mem (s t : S) : diagonalBlocks s t ∈ commutator Blocks := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hS : commutator S = ⊤ :=
    Matrix.SL2.commutator_eq_top (a := (2 : F)) (by decide) (by decide)
  have hmap (φ : S →* Blocks) (v : S) : φ v ∈ commutator Blocks := by
    have hle : (commutator S).map φ ≤ commutator Blocks := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    apply hle
    exact Subgroup.mem_map_of_mem φ (hS ▸ Subgroup.mem_top v)
  let left : S →* Blocks := {
    toFun := fun u ↦ diagonalBlocks u 1
    map_one' := rfl
    map_mul' := fun u v ↦ by
      apply Blocks.ext <;> simp [block_mul, diagonalBlocks, product, identity] }
  let right : S →* Blocks := {
    toFun := diagonalBlocks 1
    map_one' := rfl
    map_mul' := fun u v ↦ by
      apply Blocks.ext <;> simp [block_mul, diagonalBlocks, product, identity] }
  have he : left s * right t = diagonalBlocks s t := by
    change diagonalBlocks s 1 * diagonalBlocks 1 t = _
    apply Blocks.ext <;> simp [block_mul, diagonalBlocks, product, identity]
  exact he ▸ (commutator Blocks).mul_mem (hmap left s) (hmap right t)

-- In characteristic five, conjugating a shear of twice a block by a sign change
-- gives a commutator whose off-diagonal block is the original block.
private theorem twice_flip {m n : Type} (v : M m n) :
    (2 : F) • v = -((2 : F) • v) + -v := by
  ext i j
  change 2 * v i j = -(2 * v i j) + -v i j
  exact (by decide : ∀ a : F, 2 * a = -(2 * a) + -a) _

private theorem shear12_mem (a : M I J) : shear12 a ∈ commutator Blocks := by
  apply mem_derived_of_mul (x := diagonalBlocks (-1) 1) (y := shear12 ((2 : F) • a))
  apply Blocks.ext <;> simp [block_mul, product, diagonalBlocks, shear12, identity, ← twice_flip]

private theorem shear23_mem (b : M J I) : shear23 b ∈ commutator Blocks := by
  apply mem_derived_of_mul (x := diagonalBlocks (-1) 1) (y := shear23 ((2 : F) • b))
  apply Blocks.ext <;> simp [block_mul, product, diagonalBlocks, shear23, identity]
  simpa [add_comm] using congrArg Neg.neg (twice_flip b)

private theorem lastColumn_mem (d : M I J) (e : M J J) (f : M I J) :
    lastColumn d e f ∈ commutator Blocks := by
  apply mem_derived_of_mul (x := diagonalBlocks 1 (-1))
    (y := lastColumn ((2 : F) • d) ((2 : F) • e) ((2 : F) • f))
  apply Blocks.ext <;>
    simp [block_mul, product, diagonalBlocks, lastColumn, identity, ← twice_flip]

-- Elementary (1,3) blocks are commutators of (1,2) and (2,3) shears.
private theorem shear13_mem (c : M I I) : shear13 c ∈ commutator Blocks := by
  let entries : AddSubgroup (M I I) := {
    carrier := {v | shear13 v ∈ commutator Blocks}
    zero_mem' := (commutator Blocks).one_mem
    add_mem' := by
      intro u v hu hv
      have he : shear13 (u + v) = shear13 v * shear13 u := by
        apply Blocks.ext <;> simp [shear13, block_mul, identity, product]
      change shear13 (u + v) ∈ commutator Blocks
      rw [he]
      exact (commutator Blocks).mul_mem hv hu
    neg_mem' := by
      intro v hv
      have he : shear13 (-v) = (shear13 v)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        apply Blocks.ext <;> simp [shear13, block_mul, block_one, identity, product]
      change shear13 (-v) ∈ commutator Blocks
      rw [he]
      exact (commutator Blocks).inv_mem hv }
  change c ∈ entries
  rw [Matrix.matrix_eq_sum_single c]
  refine entries.sum_mem fun i _ ↦ entries.sum_mem fun j _ ↦ ?_
  change shear13 (Matrix.single i j (c i j)) ∈ commutator Blocks
  apply mem_derived_of_mul (x := shear12 (Matrix.single i 0 (c i j)))
    (y := shear23 (Matrix.single 0 j 1))
  apply Blocks.ext <;> simp [shear12, shear23, shear13, block_mul, identity, product]

private theorem blocks_perfect : Group.IsPerfect Blocks := by
  constructor
  apply top_unique
  intro x _
  have he : diagonalBlocks 1 x.t * lastColumn x.d x.e x.f * shear23 x.b * shear13 x.c *
      diagonalBlocks x.s 1 * shear12 x.a = x := by
    apply Blocks.ext <;> simp [block_mul, product, diagonalBlocks, lastColumn,
      shear23, shear13, shear12, identity]
  rw [← he]
  repeat' apply (commutator Blocks).mul_mem
  all_goals first | apply diagonal_mem | apply lastColumn_mem | apply shear23_mem |
    apply shear13_mem | apply shear12_mem

private theorem zero_of_eq_neg {m n : Type} {v : M m n} (h : v = -v) : v = 0 := by
  ext i j
  exact (by decide : ∀ u : F, u = -u → u = 0) _ (congrFun (congrFun h i) j)

-- Commuting with elementary shears detects the diagonal and (1,3) blocks.
-- Commuting with the two diagonal signs detects the remaining blocks.
private theorem blocks_center : Subgroup.center Blocks = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hc := Subgroup.mem_center_iff.mp hx
  have signS := hc (diagonalBlocks (-1) 1)
  have signT := hc (diagonalBlocks 1 (-1))
  change x = 1
  apply Blocks.ext
  · apply Subtype.ext
    ext i j
    have h := congrArg Blocks.b (hc (shear23 (Matrix.single j 0 1)))
    have he : (Matrix.single j (0 : I) (1 : F) : M J I) =
        x.s.val * (Matrix.single j 0 1 : M J I) := by
      simpa [block_mul, product, shear23, identity, add_comm] using h
    change x.s.val i j = (1 : M J J) i j
    have hv := (congrFun (congrFun he i) 0).symm
    simp only [Matrix.mul_single_apply_same, mul_one] at hv
    simpa [Matrix.single, Matrix.one_apply, Matrix.of_apply, eq_comm] using hv
  · apply Subtype.ext
    ext i j
    have h := congrArg Blocks.d (hc (lastColumn (Matrix.single 0 i 1) 0 0))
    have he : (Matrix.single (0 : I) i (1 : F) : M I J) * x.t.val = Matrix.single 0 i 1 := by
      simpa [block_mul, product, lastColumn, identity, add_comm] using h
    change x.t.val i j = (1 : M J J) i j
    have hv := congrFun (congrFun he 0) j
    simp only [Matrix.single_mul_apply_same, one_mul] at hv
    simpa [Matrix.single, Matrix.one_apply, Matrix.of_apply] using hv
  · apply zero_of_eq_neg
    simpa [block_mul, product, diagonalBlocks, identity] using congrArg Blocks.a signS
  · apply zero_of_eq_neg
    simpa [block_mul, product, diagonalBlocks, identity] using (congrArg Blocks.b signS).symm
  · ext i j
    have h := congrArg Blocks.f (hc (lastColumn (Matrix.single j 0 1) 0 0))
    have he : x.c * (Matrix.single j 0 1 : M I J) = 0 := by
      simpa [block_mul, product, lastColumn, identity] using h.symm
    change x.c i j = 0
    simpa using congrFun (congrFun he i) 0
  · apply zero_of_eq_neg
    simpa [block_mul, product, diagonalBlocks, identity] using congrArg Blocks.d signT
  · apply zero_of_eq_neg
    simpa [block_mul, product, diagonalBlocks, identity] using congrArg Blocks.e signT
  · apply zero_of_eq_neg
    simpa [block_mul, product, diagonalBlocks, identity] using congrArg Blocks.f signT

private theorem card_block (m n : ℕ) : Nat.card (M (Fin m) (Fin n)) = 5 ^ (n * m) := by
  simp only [M, Matrix, F, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul]

-- The (1,3) block has 1024 independent entries. In a conjugate, this block
-- is determined by two rectangular blocks of a conjugator and the (1,2) block.
private theorem class_bound (x : Blocks) : (conjugatesOf x).ncard ≤ 5 ^ 396 := by
  classical
  have exists_conjugator (v : conjugatesOf x) : ∃ y : Blocks, y * x = v.val * y := by
    obtain ⟨y, hy⟩ := v.property
    exact ⟨y, hy⟩
  choose y hy using exists_conjugator
  have formula (v : conjugatesOf x) :
      v.val.c = x.c + (y v).a * x.b - v.val.a * (y v).b := by
    have h := congrArg Blocks.c (hy v)
    change x.c + (y v).a * x.b + (y v).c = (y v).c + v.val.a * (y v).b + v.val.c at h
    calc
      _ = ((y v).c + v.val.a * (y v).b + v.val.c) - (y v).c - v.val.a * (y v).b := by abel
      _ = _ := by rw [← h]; abel
  let encode (v : conjugatesOf x) :=
    (v.val.s.val, v.val.t.val, v.val.a, v.val.b, v.val.d, v.val.e, v.val.f, (y v).a, (y v).b)
  have hinj : Function.Injective encode := by
    intro u v huv
    simp only [encode, Prod.mk.injEq] at huv
    obtain ⟨hs, ht, ha, hb, hd, he, hf, hya, hyb⟩ := huv
    apply Subtype.ext
    apply Blocks.ext (Subtype.ext hs) (Subtype.ext ht) ha hb _ hd he hf
    rw [formula u, formula v, hya, hyb, ha]
  have bound := Nat.card_le_card_of_injective encode hinj
  simp only [Nat.card_prod, card_block, Nat.card_coe_set_eq, ← pow_add] at bound
  simp only [Nat.reduceAdd, Nat.reduceMul] at bound
  exact bound

private theorem order_lower : 5 ^ 1024 ≤ Nat.card Blocks := by
  have hinj : Function.Injective shear13 := fun _ _ h ↦ congrArg Blocks.c h
  have h := Nat.card_le_card_of_injective shear13 hinj
  rw [card_block] at h
  simp only [Nat.reduceMul] at h
  exact h

/--
**Perfect centreless groups need not have order at most the square of the largest class size.**
It is not true that every finite group $G$ that is perfect ($[G, G] = G$) and has trivial centre
contains an element $x$ with $|G| \le |x^G|^2$, where $x^G$ is the conjugacy class of $x$. That
is, some perfect centreless finite group $G$ satisfies $|G| > n^2$, where $n$ is the largest size
of a conjugacy class of $G$.

Muliarchyk (Theorem 1.1) constructs a perfect centreless finite group of order $120 \cdot 5^{68}$
whose largest conjugacy class has size $30 \cdot 5^{32}$, so $|G| / n^2 = 250/3 > 1$; the 21st
issue of the Kourovka Notebook marks 20.30 solved ("No, not always"). The preprint acknowledges
assistance from ChatGPT.

See the module description for the counterexample using block upper triangular matrices
over $\mathbb F_5$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.30 (P. M. Neumann
and M. R. Vaughan-Lee; I. B. Gorshkov); resolution: K. Muliarchyk, Perfect centreless groups with
large centralizers, preprint (2026), Kourovka Notebook site, Theorem 1.1: an explicit perfect
centreless finite group of order 120·5^68 whose largest conjugacy class has size 30·5^32, so |G|/n²
= 250/3 > 1 (built from a class-three Baker-Campbell-Hausdorff group over F₅ and an SL₂(F₅)-action);
Theorem 6.1: no bound |G| ≤ C n^c holds for all perfect centreless finite groups; Kourovka Notebook
(21st issue), Problem 20.30: No, not always,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_20_30_solution.pdf.
-/
public theorem perfectCentrelessOrderLeMaxClassSq_refuted :
    ¬ perfectCentrelessOrderLeMaxClassSq := by
  intro h
  obtain ⟨x, hx⟩ := h Blocks blocks_perfect blocks_center
  have compare {a b : ℕ} (hab : a * 2 < b) : ((5 : ℕ) ^ a) ^ 2 < 5 ^ b := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hab
  have hpow := compare (by decide : 396 * 2 < 1024)
  exact hx.not_gt ((Nat.pow_le_pow_left (class_bound x) 2).trans_lt (hpow.trans_le order_lower))

end MathlibExt.GroupTheory.PerfectCentrelessOrderMaxClassKourovka20Problem30Wanted
