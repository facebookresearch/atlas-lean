/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Data.Finset.Sym
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The α-upper matrix

The entry formula `MetaMathlibExt.alphaUpperEntry_eq_hsymm` gives the complete homogeneous
symmetric polynomial on the interval of indices from `i + 1` to `j + 1`.

The determinant formula `MetaMathlibExt.det_alphaUpperMatrix` expresses the determinant of the
α-upper matrix as the product of the diagonal entries `α (i + 1) ^ i`. Its proof identifies
column `j` as the coefficients of `x ^ j` in a Newton basis and evaluates at `x = α (j + 1)`.
-/

namespace MetaMathlibExt

@[expose] public section

variable {R : Type*} [CommRing R]

/-- **Entries of the α-upper matrix.** Let $R$ be a commutative ring and let
$\alpha_0, \alpha_1, \alpha_2, \dots$ be a sequence in $R$ ($\alpha_0$ is never used). The
α-upper entries $u_{i,j} \in R$, for $i, j \ge 0$, are defined recursively by $u_{0,j} = 1$ for
all $j$, $u_{i,0} = 0$ for $i \ge 1$, and
$u_{i+1,j+1} = u_{i+1,j} + \alpha_{i+1} u_{i,j} + (\alpha_{j+2} - \alpha_{i+1}) u_{i,j+1}$ for
all $i, j \ge 0$.

These are the entries of the paper's matrix $\mathsf{U}_\alpha(n)$ with indices shifted to start
at $0$; in the paper's $1$-based indexing the first row is $1$, the rest of the first column is
$0$, and $\mathsf{U}_{i,j} = \mathsf{U}_{i,j-1} + \alpha_{i-1} \mathsf{U}_{i-1,j-1} +
(\alpha_j - \alpha_{i-1}) \mathsf{U}_{i-1,j}$ for $i, j \ge 2$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2,
equation (u-1-2). -/
def alphaUpperEntry (α : ℕ → R) : ℕ → ℕ → R
  | 0, _ => 1
  | _ + 1, 0 => 0
  | i + 1, j + 1 =>
      alphaUpperEntry α (i + 1) j + α (i + 1) * alphaUpperEntry α i j +
        (α (j + 2) - α (i + 1)) * alphaUpperEntry α i (j + 1)

/-- **Recurrence for the α-upper entries.** Let $R$ be a commutative ring, let $\alpha$ be a
sequence in $R$, and let $u_{i,j}$ ($i, j \ge 0$) be the α-upper entries of $\alpha$. Then for all
$i, j \ge 0$,
$u_{i+1,j+1} = u_{i+1,j} + \alpha_{i+1} u_{i,j} + (\alpha_{j+2} - \alpha_{i+1}) u_{i,j+1}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (u-1-2). -/
theorem alphaUpperEntry_succ_succ (α : ℕ → R) (i j : ℕ) :
    alphaUpperEntry α (i + 1) (j + 1) =
      alphaUpperEntry α (i + 1) j + α (i + 1) * alphaUpperEntry α i j +
        (α (j + 2) - α (i + 1)) * alphaUpperEntry α i (j + 1) := by
  rw [alphaUpperEntry]

/-- **Small α-upper entries.** Let $R$ be a commutative ring, let $\alpha$ be a sequence in $R$,
and let $u_{i,j}$ ($i, j \ge 0$) be the α-upper entries of $\alpha$. Then $u_{1,1} = \alpha_2$ and
$u_{1,2} = \alpha_2 + \alpha_3$.

Writing $\mathsf{U}_{i,j}$ for the entries of the paper's matrix $\mathsf{U}_\alpha(n)$ in its
$1$-based indexing, these are $\mathsf{U}_{2,2} = \alpha_2$ and
$\mathsf{U}_{2,3} = \alpha_2 + \alpha_3$, as in the paper's display of $\mathsf{U}_\alpha(4)$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2. -/
theorem alphaUpperEntry_one_one_one_two (α : ℕ → R) :
    alphaUpperEntry α 1 1 = α 2 ∧ alphaUpperEntry α 1 2 = α 2 + α 3 := by
  constructor
  · simp only [alphaUpperEntry]; ring
  · simp only [alphaUpperEntry]; ring

/-- **The α-upper matrix.** Let $R$ be a commutative ring, let $\alpha$ be a sequence in $R$, and
let $u_{i,j}$ ($i, j \ge 0$) be the α-upper entries of $\alpha$. For $n \ge 0$, the matrix
$\mathsf{U}_\alpha(n)$ is the $n \times n$ matrix over $R$, with rows and columns indexed by
$0, 1, \dots, n - 1$, whose $(i, j)$ entry is $u_{i,j}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2. -/
def alphaUpperMatrix (α : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => alphaUpperEntry α a b

namespace det_alphaUpperMatrix

private theorem entry_eq_zero (α : ℕ → R) {i j : ℕ} (h : j < i) :
    alphaUpperEntry α i j = 0 := by
  fun_induction alphaUpperEntry α i j with
  | case1 => omega
  | case2 => rfl
  | case3 i j ihLeft ihDiag ihUp =>
    rw [ihLeft (by omega), ihDiag (by omega)]
    rcases Nat.lt_or_eq_of_le (show j + 1 ≤ i by omega) with hj | rfl
    · simp [ihUp hj]
    · simp

/-- Horner evaluation of the first `i` entries of column `j` in the Newton basis
with successive factors `x - α k`. -/
private def horner (α : ℕ → R) (j : ℕ) (x : R) : ℕ → R
  | 0 => 0
  | i + 1 => (x - α (i + 1)) * horner α j x i + alphaUpperEntry α i j

-- The entry recurrence transports the Horner evaluation from one column to the next.
private theorem horner_step (α : ℕ → R) (j : ℕ) (x : R) (i : ℕ) :
    (x - α (j + 2)) * horner α (j + 1) x i + alphaUpperEntry α i (j + 1) =
      x * horner α j x i + alphaUpperEntry α i j := by
  induction i with
  | zero => simp [horner, alphaUpperEntry]
  | succ i ih =>
    rw [horner, horner, alphaUpperEntry_succ_succ]
    linear_combination (x - α (i + 1)) * ih

-- Column `j` gives the Newton expansion of the monomial `x ^ j`.
private theorem horner_column (α : ℕ → R) (j : ℕ) (x : R) :
    horner α j x (j + 1) = x ^ j := by
  induction j with
  | zero => simp [horner, alphaUpperEntry]
  | succ j ih =>
    rw [horner, horner_step, entry_eq_zero α (Nat.lt_succ_self j), ih, pow_succ', add_zero]

end det_alphaUpperMatrix

/-- Sum of the monomials indexed by multisets of `d` indices in `s`. -/
private def symSum (α : ℕ → R) (d : ℕ) (s : Finset ℕ) : R :=
  ∑ m ∈ s.sym d, (m.val.map α).prod

-- Split the multisets according to whether they contain the new index.
private theorem symSum_insert (α : ℕ → R) (d : ℕ) {a : ℕ} {s : Finset ℕ}
    (ha : a ∉ s) :
    symSum α (d + 1) (insert a s) =
      symSum α (d + 1) s + α a * symSum α d (insert a s) := by
  let e : Sym ℕ d ↪ Sym ℕ (d + 1) := ⟨Sym.cons a, fun _ _ => (Sym.cons_inj_right a _ _).mp⟩
  have split : (insert a s).sym (d + 1) =
      s.sym (d + 1) ∪ ((insert a s).sym d).map e := by
    ext m
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_sym_iff]
    constructor
    · intro hm
      by_cases ham : a ∈ m
      · refine Or.inr ⟨m.erase a ham, ?_, Sym.cons_erase ham⟩
        intro b hb
        exact hm b (by rw [← Sym.cons_erase ham]; exact Sym.mem_cons_of_mem hb)
      · exact Or.inl fun b hb =>
          (Finset.mem_insert.mp (hm b hb)).resolve_left (fun h => ham (h ▸ hb))
    · rintro (hm | ⟨m, hm, rfl⟩) b hb
      · exact Finset.mem_insert_of_mem (hm b hb)
      · rcases Sym.mem_cons.mp hb with rfl | hb
        · exact Finset.mem_insert_self _ _
        · exact hm b hb
  have disj : Disjoint (s.sym (d + 1)) (((insert a s).sym d).map e) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp hm'
    exact ha (Finset.mem_sym_iff.mp hm a (Sym.mem_cons_self a m))
  have he (m : Sym ℕ d) : e m = Sym.cons a m := rfl
  simp only [symSum, split, Finset.sum_union disj, Finset.sum_map, Finset.mul_sum, he,
    Sym.val_eq_coe, Sym.coe_cons, Multiset.map_cons, Multiset.prod_cons]

private theorem symSum_zero (α : ℕ → R) (s : Finset ℕ) : symSum α 0 s = 1 := by
  have h : (∅ : Sym ℕ 0) = Sym.nil := Sym.eq_nil_of_card_zero _
  simp [symSum, h]

private theorem symSum_Ioc_right (α : ℕ → R) (d lo hi : ℕ) (h : lo ≤ hi) :
    symSum α (d + 1) (Finset.Ioc lo (hi + 1)) =
      symSum α (d + 1) (Finset.Ioc lo hi) + α (hi + 1) * symSum α d (Finset.Ioc lo (hi + 1)) := by
  have hs : insert (hi + 1) (Finset.Ioc lo hi) = Finset.Ioc lo (hi + 1) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [← hs, symSum_insert α d (by simp)]

private theorem symSum_Ioc_left (α : ℕ → R) (d lo hi : ℕ) (h : lo < hi) :
    symSum α (d + 1) (Finset.Ioc lo hi) =
      symSum α (d + 1) (Finset.Ioc (lo + 1) hi) + α (lo + 1) * symSum α d (Finset.Ioc lo hi) := by
  have hs : insert (lo + 1) (Finset.Ioc (lo + 1) hi) = Finset.Ioc lo hi := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [← hs, symSum_insert α d (by simp)]

-- The interval is empty below the diagonal, so the same formula gives zero there.
private theorem alphaUpperEntry_eq_symSum (α : ℕ → R) (i j : ℕ) :
    alphaUpperEntry α i j = symSum α i (Finset.Ioc i (j + 1)) := by
  induction i generalizing j with
  | zero => rw [alphaUpperEntry.eq_1, symSum_zero]
  | succ i ih =>
    induction j with
    | zero =>
      rw [alphaUpperEntry.eq_2, Finset.Ioc_eq_empty_of_le (by omega)]
      simp [symSum]
    | succ j ihj =>
      by_cases h : i ≤ j
      · rw [alphaUpperEntry_succ_succ, ihj, ih j, ih (j + 1),
          symSum_Ioc_right α i (i + 1) (j + 1) (by omega)]
        cases i with
        | zero => simp only [symSum_zero, mul_one]; ring
        | succ i =>
          -- Expand the previous row's wider interval at both ends. The terms
          -- with both endpoint factors cancel in the entry recurrence.
          have hr := symSum_Ioc_right α i (i + 1) (j + 1) (by omega)
          have hl := symSum_Ioc_left α i (i + 1) (j + 2) (by omega)
          linear_combination α (j + 2) * hl - α (i + 2) * hr
      · rw [det_alphaUpperMatrix.entry_eq_zero α (by omega),
          Finset.Ioc_eq_empty_of_le (by omega)]
        simp [symSum]

/-- **α-upper entries are complete homogeneous symmetric polynomials.** Let $R$ be a commutative
ring, let $\alpha$ be a sequence in $R$, and let $u_{i,j}$ ($i, j \ge 0$) be the α-upper entries
of $\alpha$. For all $i \le j$, $u_{i,j} = h_i(\alpha_{i+1}, \alpha_{i+2}, \dots, \alpha_{j+1})$,
where $h_i$ is the complete homogeneous symmetric polynomial of degree $i$ in $j - i + 1$
variables.

Writing $\mathsf{U}_{i,j}$ for the entries of the paper's matrix $\mathsf{U}_\alpha(n)$ in its
$1$-based indexing, this reads $\mathsf{U}_{i,j} = h_{i-1}(\alpha_i, \dots, \alpha_j)$ for
$j \ge i \ge 1$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 1
(`jis-2026-26.5.4-lem-1`). -/
theorem alphaUpperEntry_eq_hsymm (α : ℕ → R) {i j : ℕ} (hij : i ≤ j) :
    alphaUpperEntry α i j =
      MvPolynomial.eval (fun t : Fin (j - i + 1) => α (i + 1 + t))
        (MvPolynomial.hsymm (Fin (j - i + 1)) R i) := by
  let e : Fin (j - i + 1) ↪ ℕ :=
    ⟨fun t => i + 1 + t, fun a b h => Fin.ext (Nat.add_left_cancel h)⟩
  have hs : Finset.univ.map e = Finset.Ioc i (j + 1) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨t, ht⟩, rfl⟩
      change i < i + 1 + t ∧ i + 1 + t ≤ j + 1
      omega
    · intro hk
      refine ⟨⟨k - (i + 1), by omega⟩, ?_⟩
      change i + 1 + (k - (i + 1)) = k
      omega
  have he (t : Fin (j - i + 1)) : e t = i + 1 + t := rfl
  rw [alphaUpperEntry_eq_symSum, symSum, ← hs, Finset.sym_map, Finset.sum_map,
    Finset.sym_univ, MvPolynomial.hsymm, map_sum]
  simp only [Function.Embedding.coeFn_mk, Sym.val_eq_coe, Sym.coe_map, Multiset.map_map,
    ← Multiset.prod_hom', MvPolynomial.eval_X, Function.comp_def, he]

/-- **Determinant of the α-upper matrix.** Let $R$ be a commutative ring and let $\alpha$ be a
sequence in $R$. For every $n \ge 0$, the determinant of the $n \times n$ α-upper matrix
$\mathsf{U}_\alpha(n)$ is $\det \mathsf{U}_\alpha(n) = \prod_{i=1}^{n} \alpha_i^{i-1}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 1
(`jis-2026-26.5.4-lem-1`). -/
theorem det_alphaUpperMatrix (α : ℕ → R) (n : ℕ) :
    (alphaUpperMatrix α n).det = ∏ i : Fin n, α (i + 1) ^ (i : ℕ) := by
  have htri : (alphaUpperMatrix α n).IsUpperTriangular :=
    fun {_ _} hij => det_alphaUpperMatrix.entry_eq_zero α hij
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_congr rfl
  intro i _
  simpa [det_alphaUpperMatrix.horner, alphaUpperMatrix] using
    det_alphaUpperMatrix.horner_column α (i : ℕ) (α (i + 1))

end

end MetaMathlibExt
