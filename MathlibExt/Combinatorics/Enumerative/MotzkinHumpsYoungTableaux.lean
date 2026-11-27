/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.MotzkinHumpPeakHeight
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-!
# Hook tableau counts as differences of hump counts

The counts of hook tableaux of two consecutive sizes add up to the increase in the number
of marked Motzkin humps at a fixed height.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Standard Young tableau.** A standard Young tableau of order $n$ is encoded by a map $T$ that
assigns to each entry $i \in \{0, \dots, n-1\}$ a cell $T(i) = (r_i, c_i)$ with row and column
indices in $\{0, \dots, n-1\}$. The map $T$ is a standard Young tableau when it is injective
and, for every entry $i$ and every cell $(r, c)$ with $r \le r_i$ and $c \le c_i$, there is an
entry $j \le i$ with $T(j) = (r, c)$.

It follows that for every $m \le n$ the cells of the entries $0, \dots, m-1$ form a Young
diagram, and that entries increase strictly along rows and down columns.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsStandardYoungTableau (n : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  Function.Injective T ∧
    ∀ i c, c.1 ≤ (T i).1 → c.2 ≤ (T i).2 → ∃ j, j ≤ i ∧ T j = c

/-- **Unfolding the standard Young tableau condition.** Let $T$ assign to each entry
$i \in \{0, \dots, n-1\}$ a cell $T(i) = (r_i, c_i)$ with row and column indices in
$\{0, \dots, n-1\}$. Then $T$ is a standard Young tableau of order $n$ if and only if $T$ is
injective and, for every entry $i$ and every cell $(r, c)$ with $r \le r_i$ and $c \le c_i$,
there is an entry $j \le i$ with $T(j) = (r, c)$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isStandardYoungTableau_iff (n : ℕ) (T : Fin n → Fin n × Fin n) :
    IsStandardYoungTableau n T ↔
      Function.Injective T ∧
        ∀ i c, c.1 ≤ (T i).1 → c.2 ≤ (T i).2 → ∃ j, j ≤ i ∧ T j = c := by
  rfl

/-- Membership in the finite-cell SYT encoding is decidable by finite quantification.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsStandardYoungTableau (n : ℕ)
    (T : Fin n → Fin n × Fin n) : Decidable (IsStandardYoungTableau n T) := by
  unfold IsStandardYoungTableau Function.Injective
  infer_instance

/-- **Tableaux in the $(2,1)$-hook.** Let $T$ assign to each entry $i < n$ a cell $(r_i, c_i)$
with zero-based row $r_i < n$ and column $c_i < n$. Then $T$ lies in the $(2,1)$-hook when no
entry occupies a cell whose row is at least $2$ and whose column is at least $1$, that is, when
no $i$ has both $r_i \ge 2$ and $c_i \ge 1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsInTwoOneHook (n : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  ∀ i, ¬(2 ≤ (T i).1.val ∧ 1 ≤ (T i).2.val)

/-- **Characterization of tableaux in the $(2,1)$-hook.** Let $T$ assign to each entry $i < n$ a
cell $(r_i, c_i)$ with zero-based row $r_i < n$ and column $c_i < n$. Then $T$ lies in the
$(2,1)$-hook if and only if for no entry $i$ do both $r_i \ge 2$ and $c_i \ge 1$ hold.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isInTwoOneHook_iff (n : ℕ) (T : Fin n → Fin n × Fin n) :
    IsInTwoOneHook n T ↔ ∀ i, ¬(2 ≤ (T i).1.val ∧ 1 ≤ (T i).2.val) := by
  rfl

/-- Membership in the `(2,1)`-hook is decidable by inspecting the finitely many entries.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsInTwoOneHook (n : ℕ) (T : Fin n → Fin n × Fin n) :
    Decidable (IsInTwoOneHook n T) := by
  unfold IsInTwoOneHook
  infer_instance

/-- **Row length of a tableau.** For a natural number $n$, let $T$ assign to each entry
$i \in \{0, \dots, n-1\}$ a cell $T(i)$, given by a zero-based row index and a zero-based column
index, both in $\{0, \dots, n-1\}$. For a natural number $r$, the length of row $r$ is the number
of entries $i$ whose cell $T(i)$ lies in row $r$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def tableauRowLength (n : ℕ) (T : Fin n → Fin n × Fin n) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (T i).1.val = r).card

/-- **First-two-row difference of a tableau.** Let $T$ assign to each entry $i < n$ a cell
$(r_i, c_i)$ with zero-based row $r_i < n$ and column $c_i < n$, and let $\lambda_1$ and
$\lambda_2$ be the numbers of entries $i$ with $r_i = 0$ and with $r_i = 1$ respectively. For a
natural number $k$, $T$ has first-two-row difference $k$ when $\lambda_1 = \lambda_2 + k$, that
is, when $\lambda_1 - \lambda_2 = k$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def HasFirstTwoRowDifference (n k : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  tableauRowLength n T 0 = tableauRowLength n T 1 + k

/-- **Characterization of the first-two-row difference.** Let $T$ assign to each entry $i < n$ a
cell $(r_i, c_i)$ with zero-based row $r_i < n$ and column $c_i < n$, and let $\lambda_1$ and
$\lambda_2$ be the numbers of entries $i$ with $r_i = 0$ and with $r_i = 1$ respectively. For a
natural number $k$, $T$ has first-two-row difference $k$ if and only if
$\lambda_1 = \lambda_2 + k$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem hasFirstTwoRowDifference_iff (n k : ℕ) (T : Fin n → Fin n × Fin n) :
    HasFirstTwoRowDifference n k T ↔
      tableauRowLength n T 0 = tableauRowLength n T 1 + k := by
  rfl

/-- The first-two-row cardinality equation is decidable.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableHasFirstTwoRowDifference (n k : ℕ)
    (T : Fin n → Fin n × Fin n) : Decidable (HasFirstTwoRowDifference n k T) := by
  unfold HasFirstTwoRowDifference
  infer_instance

/-- **Standard Young tableaux in the $(2,1)$-hook with given row difference.** For natural numbers
$n$ and $k$, $\mathrm{SYT}_k(2,1;n)$ is the number of standard Young tableaux of order $n$ whose
shape $\lambda$ lies in the $(2,1)$-hook, that is $\lambda_3 \le 1$, and whose first two row
lengths satisfy $\lambda_1 = \lambda_2 + k$ (a missing row has length $0$).

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def sytHookCount (n k : ℕ) : ℕ :=
  Fintype.card {T : Fin n → Fin n × Fin n //
    IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧ HasFirstTwoRowDifference n k T}

/-- **Motzkin peak.** Let $p$ be a word of length $n$ in the steps $D$, $F$, $U$, let
$k \in \mathbb{N}$, and let $i, j \in \{0, \dots, n-1\}$. The pair $(i, j)$ is a peak of height
$k$ in $p$ when it is a hump of height $k$ in $p$ and $j = i + 1$, that is, when the down step
$p_j$ immediately follows the up step $p_i$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinPeak (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  IsMotzkinHump n k p i j ∧ i.val + 1 = j.val

/-- **Peaks are humps with adjacent endpoints.** Let $p$ be a word of length $n$ in the steps $D$,
$F$, $U$, let $k \in \mathbb{N}$, and let $i, j \in \{0, \dots, n-1\}$. Then $(i, j)$ is a peak of
height $k$ in $p$ if and only if $(i, j)$ is a hump of height $k$ in $p$ and $j = i + 1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinPeak_iff (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) :
    IsMotzkinPeak n k p i j ↔ IsMotzkinHump n k p i j ∧ i.val + 1 = j.val := by
  rfl

/-- **Paths whose last non-flat step is up.** A word $p = p_0 p_1 \cdots p_{n-1}$ of length $n$
in the steps $U$ (up), $F$ (flat) and $D$ (down) has last non-flat step up when some position
$i$ has $p_i = U$ and every later step $p_j$ with $j > i$ is $F$. In particular, such a word
contains an up step.

Among the Motzkin prefixes of length $n$ ending at height $h$ (words that never go below height
$0$ and end at height $h$), these words form the paper's set $\mathcal{M}^{*U}_{n,h}$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def LastNonflatStepUp (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, p i = 2 ∧ ∀ j, i < j → p j = 1

/-- **Characterization of words whose last non-flat step is up.** Let $p = p_0 p_1 \cdots p_{n-1}$
be a word of length $n$ in the steps $D$, $F$, $U$. Then the last non-flat step of $p$ is $U$ if
and only if there is a position $i$ with $p_i = U$ such that $p_j = F$ for every position $j > i$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem lastNonflatStepUp_iff (n : ℕ) (p : Fin n → Fin 3) :
    LastNonflatStepUp n p ↔ ∃ i, p i = 2 ∧ ∀ j, i < j → p j = 1 := by
  rfl

/-- **Paths whose first non-up step is down.** Write a path of length $n$ as a sequence of steps
$p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as $0$, $1$, $2$. The
path has first non-up step down when there is a position $i$ with $p_i = D$ and $p_j = U$ for
every $j < i$. In particular, a path all of whose steps are up steps, including the empty path,
does not qualify.

For a Motzkin prefix ending at height $h$, this is membership in the paper's set
$\mathcal{M}^{D*}_{n,h}$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def FirstNonupStepDown (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, p i = 0 ∧ ∀ j, j < i → p j = 2

/-- **Characterization of paths whose first non-up step is down.** Write a path of length $n$ as
a sequence of steps $p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as
$0$, $1$, $2$. The path has first non-up step $D$ if and only if there is a position $i$ with
$p_i = D$ and $p_j = U$ for every $j < i$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem firstNonupStepDown_iff (n : ℕ) (p : Fin n → Fin 3) :
    FirstNonupStepDown n p ↔ ∃ i, p i = 0 ∧ ∀ j, j < i → p j = 2 := by
  rfl

/-- **Paths ending with an up step.** Write a path of length $n$ as a sequence of steps
$p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as $0$, $1$, $2$. The
path ends with an up step when it has a last position, that is, some $i < n$ with $i + 1 = n$,
and $p_i = U$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def EndsWithUp (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, i.val + 1 = n ∧ p i = 2

/-- **Characterization of paths ending with an up step.** Write a path of length $n$ as a
sequence of steps $p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as
$0$, $1$, $2$. The path ends with an up step if and only if there is a position $i < n$ with
$i + 1 = n$ and $p_i = U$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public theorem endsWithUp_iff (n : ℕ) (p : Fin n → Fin 3) :
    EndsWithUp n p ↔ ∃ i, i.val + 1 = n ∧ p i = 2 := by
  rfl

/-- A computationally shallow expansion of `H_{n,k}` that enumerates the path and
the two marked positions in nested indicator sums.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def motzkinHumpCountExpanded (n k : ℕ) : ℕ :=
  ∑ p : Fin n → Fin 3, ∑ i : Fin n, ∑ j : Fin n,
    if IsMotzkinPrefix n 0 p ∧ IsMotzkinHump n k p i j then 1 else 0

/-- The nested indicator expansion computes the defining distinguished-hump cardinality.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private theorem motzkinHumpCount_eq_expanded (n k : ℕ) :
    motzkinHumpCount n k = motzkinHumpCountExpanded n k := by
  classical
  rw [motzkinHumpCount, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rfl

/-- **Motzkin generating function.** The Motzkin series is the formal power series
$M(x) = \sum_{n \ge 0} m_n x^n$ in $\mathbb{Z}[[x]]$, where $m_n$ is the $n$-th Motzkin number.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def motzkinSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (motzkinNumber n : ℤ))

/-- A cell-valued map is equivalently the pair of its row and column coordinate maps.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def tableauCoordinateEquiv (n : ℕ) :
    (Fin n → Fin n × Fin n) ≃ (Fin n → Fin n) × (Fin n → Fin n) where
  toFun T := (fun i => (T i).1, fun i => (T i).2)
  invFun rc := fun i => (rc.1 i, rc.2 i)
  left_inv T := by
    funext i
    exact Prod.eta (T i)
  right_inv rc := by
    exact Prod.ext (by rfl) (by rfl)

/-- Restricting `tableauCoordinateEquiv` gives an equivalence between valid tableaux
and pairs of coordinate maps satisfying the same tableau predicate.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def sytHookSubtypeEquiv (n k : ℕ) :
    {T : Fin n → Fin n × Fin n //
      IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧ HasFirstTwoRowDifference n k T} ≃
    {rc : (Fin n → Fin n) × (Fin n → Fin n) //
      let T := fun i => (rc.1 i, rc.2 i)
      IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧
        HasFirstTwoRowDifference n k T} where
  toFun T := ⟨tableauCoordinateEquiv n T.val, by simpa [tableauCoordinateEquiv] using T.property⟩
  invFun rc := ⟨(tableauCoordinateEquiv n).symm rc.val, by
    simpa [tableauCoordinateEquiv] using rc.property⟩
  left_inv T := by
    apply Subtype.ext
    exact (tableauCoordinateEquiv n).left_inv T.val
  right_inv rc := by
    apply Subtype.ext
    exact (tableauCoordinateEquiv n).right_inv rc.val

/-- A computationally shallow expansion of `SYT_k(2,1;n)` that independently
enumerates the row and column coordinate maps.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def sytHookCountExpanded (n k : ℕ) : ℕ :=
  ∑ rows : Fin n → Fin n, ∑ cols : Fin n → Fin n,
    let T := fun i => (rows i, cols i)
    if IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧
        HasFirstTwoRowDifference n k T then 1 else 0

/-- The nested coordinate-map expansion computes the defining SYT cardinality.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private theorem sytHookCount_eq_expanded (n k : ℕ) :
    sytHookCount n k = sytHookCountExpanded n k := by
  classical
  rw [sytHookCount, Fintype.card_congr (sytHookSubtypeEquiv n k),
    Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rfl

/-- **Motzkin paths with a marked hump, over all heights.** For a natural number $n$, this is
the set of triples $(k, P, h)$ where $k$ is a natural number with
$1 \le k \le \lfloor n/2 \rfloor$, $P$ is a Motzkin path of length $n$ (a word of $n$ steps
$U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$ that ends at height $0$ and never goes below height
$0$), and $h$ is a hump of height $k$ in $P$: an up step and a later down step with only flat
steps between them, where the up step ends at height $k$, recorded by the positions of its two
steps.

This is the paper's disjoint union $\bigcup_{1 \le k \le \lfloor n/2 \rfloor} \mathcal{H}_{n,k}$,
keeping the height index $k$ with each marked path.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def MotzkinHumpFamily (n : ℕ) :=
  {q : ℕ × ((Fin n → Fin 3) × Fin n × Fin n) //
    1 ≤ q.1 ∧ q.1 ≤ n / 2 ∧ IsMotzkinPrefix n 0 q.2.1 ∧
      IsMotzkinHump n q.1 q.2.1 q.2.2.1 q.2.2.2}

/-- **Motzkin prefixes of even height whose last non-flat step is up.** Use the steps
$U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$, and call a word in these steps a Motzkin prefix if
none of its initial segments ends below height $0$. For a natural number $n$, this is the set
of pairs $(k, p)$ where $k$ is a natural number with $1 \le k \le \lfloor n/2 \rfloor$ and $p$
is a Motzkin prefix of length $n$ ending at height $2k$ that contains a $U$ after which every
step is $F$.

This is the paper's disjoint union
$\bigcup_{1 \le k \le \lfloor n/2 \rfloor} \mathcal{M}^{*U}_{n,2k}$, keeping the index $k$ with
each path.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def MotzkinLastUpEvenFamily (n : ℕ) :=
  {q : ℕ × (Fin n → Fin 3) //
    1 ≤ q.1 ∧ q.1 ≤ n / 2 ∧ IsMotzkinPrefix n (2 * q.1) q.2 ∧
      LastNonflatStepUp n q.2}

/-- **Motzkin prefixes whose first non-up step is down.** Use the steps $U = (1,1)$,
$F = (1,0)$ and $D = (1,-1)$, and call a word in these steps a Motzkin prefix if none of its
initial segments ends below height $0$. For a natural number $n$, this is the set of pairs
$(k, p)$ where $k$ is a natural number with $k \le n - 2$ and $p$ is a Motzkin prefix of length
$n$ ending at height $k$ whose first step other than $U$ exists and is $D$.

This is the paper's disjoint union $\bigcup_{0 \le k \le n-2} \mathcal{M}^{D*}_{n,k}$, keeping
the index $k$ with each path.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 6 (`jis-2025-25.8.1-lem-6`).
-/
public def MotzkinFirstDownFamily (n : ℕ) :=
  {q : ℕ × (Fin n → Fin 3) //
    q.1 + 2 ≤ n ∧ IsMotzkinPrefix n q.1 q.2 ∧ FirstNonupStepDown n q.2}

/-- **Hook tableaux of order 3 with row difference 1.** The number $\mathrm{SYT}_1(2,1;3)$ of
standard Young tableaux of order $3$ in the $(2,1)$-hook whose first row is longer than its
second row by exactly $1$ equals $2$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_three_one : sytHookCount 3 1 = 2 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- **Hook tableaux of order 3 with row difference 0.** The number $\mathrm{SYT}_0(2,1;3)$ of
standard Young tableaux of order $3$ in the $(2,1)$-hook whose first two rows have the same
length equals $1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_three_zero : sytHookCount 3 0 = 1 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- **Hook tableaux of order 2 with row difference 1.** The number $\mathrm{SYT}_1(2,1;2)$ of
standard Young tableaux of order $2$ in the $(2,1)$-hook whose first row is longer than its
second row by exactly $1$ equals $0$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_two_one : sytHookCount 2 1 = 0 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- **Humps of height one in Motzkin paths of length four.** Let $H_{n,k}$ be the number of
pairs $(P, h)$ where $P$ is a Motzkin path of length $n$ and $h$ is a hump of height $k$ in $P$,
that is, an up step and a later down step with only flat steps between them, where the up step
ends at height $k$. Then $H_{4,1} = 8$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Hump-count table.
-/
public theorem motzkinHumpCount_four_one : motzkinHumpCount 4 1 = 8 := by
  rw [motzkinHumpCount_eq_expanded]
  decide

namespace sytHookCount_add_eq_humpCount_sub

private abbrev Cell (N : ℕ) := Fin N × Fin N

private def coord {N : ℕ} (x : Cell N) : ℕ × ℕ := (x.1.val, x.2.val)

private theorem coord_injective {N : ℕ} : Function.Injective (@coord N) := by
  intro x y h
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

-- After filling the first two rows to lengths a and b, the remaining c cells form a column.
private def shape (a b c : ℕ) : Set (ℕ × ℕ) :=
  {x | (x.1 = 0 ∧ x.2 < a) ∨ (x.1 = 1 ∧ x.2 < b) ∨
    (2 ≤ x.1 ∧ x.1 < c + 2 ∧ x.2 = 0)}

private def Addable (S : Set (ℕ × ℕ)) (x : ℕ × ℕ) : Prop :=
  x ∉ S ∧ (x.1 < 2 ∨ x.2 = 0) ∧
    ∀ y : ℕ × ℕ, y.1 ≤ x.1 → y.2 ≤ x.2 → y = x ∨ y ∈ S

private theorem addable_shape {a b c : ℕ} (hba : b ≤ a) (hc : c = 0 ∨ 0 < b)
    (x : ℕ × ℕ) :
    Addable (shape a b c) x ↔ x = (0, a) ∨ (b < a ∧ x = (1, b)) ∨
      (0 < b ∧ x = (c + 2, 0)) := by
  obtain ⟨r, s⟩ := x
  simp only [Addable, shape, Set.mem_ofPred_eq, Prod.mk.injEq, Prod.forall]
  constructor
  · rintro ⟨hout, hhook, hpred⟩
    have left := hpred r (s - 1) (by omega) (by omega)
    have above := hpred (r - 1) s (by omega) (by omega)
    have second := hpred 1 0
    omega
  · rintro (⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩) <;>
      refine ⟨by omega, by omega, fun i j hi hj => ?_⟩ <;> omega

private theorem shape_top (a b c : ℕ) :
    insert (0, a) (shape a b c) = shape (a + 1) b c := by
  ext ⟨r, s⟩
  simp only [Set.mem_insert_iff, shape, Set.mem_ofPred_eq, Prod.mk.injEq]
  omega

private theorem shape_second (a b c : ℕ) :
    insert (1, b) (shape a b c) = shape a (b + 1) c := by
  ext ⟨r, s⟩
  simp only [Set.mem_insert_iff, shape, Set.mem_ofPred_eq, Prod.mk.injEq]
  omega

private theorem shape_lower (a b c : ℕ) :
    insert (c + 2, 0) (shape a b c) = shape a b (c + 1) := by
  ext ⟨r, s⟩
  simp only [Set.mem_insert_iff, shape, Set.mem_ofPred_eq, Prod.mk.injEq]
  omega

private def Admissible {n N : ℕ} (S : Set (ℕ × ℕ)) (T : Fin n → Cell N) : Prop :=
  ∀ i, Addable (S ∪ {y | ∃ j < i, coord (T j) = y}) (coord (T i))

private theorem admissible_cons {n N : ℕ} (S : Set (ℕ × ℕ)) (x : Cell N)
    (T : Fin n → Cell N) :
    Admissible S (Fin.cons x T) ↔ Addable S (coord x) ∧ Admissible (insert (coord x) S) T := by
  unfold Admissible
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hzero : S ∪ {y | ∃ j : Fin (n + 1), j < 0 ∧
      coord ((Fin.cons x T : Fin (n + 1) → Cell N) j) = y} = S := by
    ext y
    simp
  have hsucc (i : Fin n) :
      S ∪ {y | ∃ j < i.succ, coord ((Fin.cons x T : Fin (n + 1) → Cell N) j) = y} =
      insert (coord x) S ∪ {y | ∃ j < i, coord (T j) = y} := by
    ext y
    simp [Fin.exists_fin_succ, eq_comm]
    tauto
  simp only [hzero, hsucc]

private def rowSize {n N : ℕ} (T : Fin n → Cell N) (r : ℕ) : ℕ :=
  ∑ i, if (T i).1.val = r then 1 else 0

private theorem rowSize_cons {n N : ℕ} (T : Fin n → Cell N) (x : Cell N) (r : ℕ) :
    rowSize (Fin.cons x T) r = (if x.1.val = r then 1 else 0) + rowSize T r := by
  unfold rowSize
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

private theorem admissible_empty {n : ℕ} (T : Fin n → Cell n) :
    Admissible ∅ T ↔ IsStandardYoungTableau n T ∧ IsInTwoOneHook n T := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j he
      by_contra hn
      rcases lt_or_gt_of_ne hn with hij | hji
      · exact (h j).1 (Or.inr ⟨i, hij, congrArg coord he⟩)
      · exact (h i).1 (Or.inr ⟨j, hji, congrArg coord he.symm⟩)
    · intro i y hr hs
      rcases (h i).2.2 (coord y) hr hs with he | he | ⟨j, hj, he⟩
      · exact ⟨i, le_rfl, (coord_injective he).symm⟩
      · exact False.elim he
      · exact ⟨j, hj.le, coord_injective he⟩
    · intro i
      have hh := (h i).2.1
      simp only [coord] at hh
      omega
  · rintro ⟨⟨hinj, hclosed⟩, hhook⟩ i
    refine ⟨?_, ?_, ?_⟩
    · rintro (he | ⟨j, hj, he⟩)
      · exact he
      · exact hj.ne (hinj (coord_injective he))
    · have hh := hhook i
      simp only [coord]
      omega
    · rintro ⟨r, s⟩ hr hs
      let y : Cell n := (⟨r, lt_of_le_of_lt hr (T i).1.isLt⟩,
        ⟨s, lt_of_le_of_lt hs (T i).2.isLt⟩)
      obtain ⟨j, hj, hTy⟩ := hclosed i y hr hs
      rcases hj.lt_or_eq with hj | rfl
      · exact Or.inr (Or.inr ⟨j, hj, congrArg coord hTy⟩)
      · exact Or.inl (congrArg coord hTy).symm

private noncomputable def completions (N n : ℕ) (S : Set (ℕ × ℕ)) (a b k : ℕ) : ℕ := by
  classical
  exact ∑ T : Fin n → Cell N,
    if Admissible S T ∧ a + rowSize T 0 = b + rowSize T 1 + k then 1 else 0

private noncomputable abbrev fills (N n a b c k : ℕ) :=
  completions N n (shape a b c) a b k

private theorem fills_empty (n k : ℕ) : fills n n 0 0 0 k = sytHookCount n k := by
  classical
  have hempty : shape 0 0 0 = ∅ := by
    ext ⟨r, s⟩
    simp [shape]
    omega
  have hr (T : Fin n → Cell n) (r : ℕ) : rowSize T r = tableauRowLength n T r := by
    simp [rowSize, tableauRowLength]
  unfold fills completions sytHookCount
  rw [hempty, Fintype.card_subtype, Finset.card_filter]
  simp only [admissible_empty, hr, HasFirstTwoRowDifference, zero_add, and_assoc]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with h <;> simp [h]

private theorem completions_zero (N : ℕ) (S : Set (ℕ × ℕ)) (a b k : ℕ) :
    completions N 0 S a b k = if a = b + k then 1 else 0 := by
  classical
  simp [completions, Admissible, rowSize]

open scoped Classical in
private theorem completions_succ (N n : ℕ) (S : Set (ℕ × ℕ)) (a b k : ℕ) :
    completions N (n + 1) S a b k =
      ∑ x : Cell N, if Addable S (coord x) then
        completions N n (insert (coord x) S)
          (a + if x.1.val = 0 then 1 else 0) (b + if x.1.val = 1 then 1 else 0) k
      else 0 := by
  classical
  unfold completions
  let e := Fin.consEquiv (n := n) (fun _ => Cell N)
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  change (∑ T : Fin n → Cell N, if Admissible S (Fin.cons x T) ∧
    a + rowSize (Fin.cons x T) 0 = b + rowSize (Fin.cons x T) 1 + k then 1 else 0) = _
  simp only [admissible_cons, rowSize_cons, ← add_assoc]
  by_cases hx : Addable S (coord x) <;> simp [hx]

private theorem sum_cell (N r s v : ℕ) :
    (∑ x : Cell N, if coord x = (r, s) then v else 0) =
      if r < N ∧ s < N then v else 0 := by
  classical
  split_ifs with h
  · let x : Cell N := (⟨r, h.1⟩, ⟨s, h.2⟩)
    have he (y : Cell N) : coord y = (r, s) ↔ y = x := by
      change coord y = coord x ↔ _
      exact coord_injective.eq_iff
    simp [he]
  · apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ _
    have hne : coord (i, j) ≠ (r, s) := by
      intro he
      have hi : i.val = r := congrArg Prod.fst he
      have hj : j.val = s := congrArg Prod.snd he
      exact h ⟨hi ▸ i.isLt, hj ▸ j.isLt⟩
    simp [hne]

-- A hook shape grows at the end of either of the first two rows, or below the first column.
private theorem fills_succ {N n a b c k : ℕ} (hN : a + b + c + (n + 1) = N)
    (hba : b ≤ a) (hc : c = 0 ∨ 0 < b) :
    fills N (n + 1) a b c k =
      fills N n (a + 1) b c k + (if b < a then fills N n a (b + 1) c k else 0) +
        (if 0 < b then fills N n a b (c + 1) k else 0) := by
  classical
  unfold fills
  rw [completions_succ]
  calc
    _ = ∑ x : Cell N,
        ((if coord x = (0, a) then fills N n (a + 1) b c k else 0) +
        (if coord x = (1, b) then (if b < a then fills N n a (b + 1) c k else 0) else 0) +
        (if coord x = (c + 2, 0) then (if 0 < b then fills N n a b (c + 1) k else 0)
          else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      change (if Addable _ (coord x) then completions N n (insert (coord x) _)
        (a + if (coord x).1 = 0 then 1 else 0) (b + if (coord x).1 = 1 then 1 else 0) k
        else 0) = _
      rw [addable_shape hba hc]
      by_cases h : coord x = (0, a)
      · simp [h, fills, shape_top]
      by_cases d : coord x = (1, b)
      · by_cases hd : b < a <;> simp [d, hd, fills, shape_second]
      by_cases f : coord x = (c + 2, 0)
      · by_cases hf : 0 < b <;> simp [f, hf, fills, shape_lower]
      · simp [h, d, f]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_cell, sum_cell, sum_cell]
      have ht : 0 < N ∧ a < N := by omega
      have hs : b < a → 1 < N ∧ b < N := by omega
      have hl : 0 < b → c + 2 < N ∧ 0 < N := by omega
      by_cases hd : b < a <;> by_cases hf : 0 < b <;> simp_all [fills]

-- A walk can be counted by its last step or by its first. Down steps require positive height.
private theorem walk_end (n a k : ℕ) : walkCount (n + 1) a k =
    walkCount n a (k + 1) + (if 0 < k then walkCount n a (k - 1) else 0) + walkCount n a k := by
  cases k <;> simp [walkCount, add_comm, add_left_comm, add_assoc]

private theorem walk_start (n a k : ℕ) : walkCount (n + 1) a k =
    walkCount n (a + 1) k + (if 0 < a then walkCount n (a - 1) k else 0) + walkCount n a k := by
  induction n generalizing a k with
  | zero =>
    rw [walk_end]
    simp only [walkCount]
    split_ifs <;> omega
  | succ n ih =>
    rw [walk_end]
    conv_lhs => simp only [ih]
    conv_rhs => simp only [walk_end]
    split_ifs <;> omega

-- Once the second row is occupied, the three possible additions are precisely Motzkin steps.
private theorem fills_with_second {N n a b c k : ℕ} (hN : a + b + c + n = N)
    (hba : b ≤ a) (hb : 0 < b) : fills N n a b c k = walkCount n (a - b) k := by
  induction n generalizing a b c with
  | zero =>
    rw [fills, completions_zero, walkCount]
    split_ifs <;> omega
  | succ n ih =>
    rw [fills_succ hN hba (Or.inr hb), ite_eq_left hb, walk_start,
      ih (by omega) (by omega) hb, ih (by omega) hba hb]
    rw [show a + 1 - b = a - b + 1 by omega]
    by_cases h : b < a
    · rw [ite_eq_left h, ite_eq_left (by omega), ih (by omega) (by omega) (by omega)]
      rw [show a - (b + 1) = a - b - 1 by omega]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

-- With only the first row occupied, the first move off that row must start the second row.
private def fromRow : ℕ → ℕ → ℕ → ℕ
  | 0, a, k => if a = k then 1 else 0
  | n + 1, a, k => fromRow n (a + 1) k + if 0 < a then walkCount n (a - 1) k else 0

private theorem fills_from_row (n a k : ℕ) :
    fills (a + n) n a 0 0 k = fromRow n a k := by
  induction n generalizing a with
  | zero => simp [fills, completions_zero, fromRow]
  | succ n ih =>
    rw [fills_succ (by omega) (by omega) (Or.inl rfl), fromRow]
    rw [show a + (n + 1) = a + 1 + n by omega, ih]
    by_cases h : 0 < a
    · simp only [h, ite_true, lt_irrefl, ite_false, add_zero]
      rw [fills_with_second (by omega) (by omega) (by omega)]
    · simp [h]

private theorem syt_eq_fromRow (n k : ℕ) : sytHookCount n k = fromRow n 0 k := by
  simpa only [zero_add, fills_empty] using fills_from_row n 0 k

-- Adding consecutive sizes cancels the restriction on the first move off the top row.
-- The extra term counts the tableau with just one row, of final length a + n + 1.
private theorem fromRow_add (n a k : ℕ) :
    fromRow (n + 1) a k + fromRow n a k =
      walkCount n a k + (if 0 < a then walkCount n (a - 1) k else 0) +
        (if a + n + 1 = k then 1 else 0) := by
  induction n generalizing a with
  | zero =>
    simp only [fromRow, walkCount, add_zero]
    omega
  | succ n ih =>
    change (fromRow (n + 1) (a + 1) k + (if 0 < a then walkCount (n + 1) (a - 1) k else 0)) +
      (fromRow n (a + 1) k + (if 0 < a then walkCount n (a - 1) k else 0)) = _
    rw [walk_start n a k]
    have h := ih (a + 1)
    simp only [Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel] at h
    rw [show a + (n + 1) + 1 = (a + 1) + n + 1 by omega]
    omega

end sytHookCount_add_eq_humpCount_sub

/-- **Hook tableau counts as differences of hump counts.** For natural numbers $m$ and $j$, let
$\mathrm{SYT}_j(2,1;m)$ be the number of standard Young tableaux of order $m$ in the
$(2,1)$-hook whose first row is longer than its second row by exactly $j$, and let $H_{m,j}$ be
the number of Motzkin paths of length $m$ with one distinguished hump of height $j$ (a hump is
an up step followed by flat steps and then a down step; its height is the height reached by the
up step). For natural numbers $n$ and $k$ with $1 \le k \le \lfloor n/2 \rfloor$,
$$
\mathrm{SYT}_{2k-1}(2,1;n+1) + \mathrm{SYT}_{2k-1}(2,1;n) = H_{n+1,k} - H_{n,k},
$$
where the subtraction is taken in the integers.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 10 (`jis-2025-25.8.1-cor-10`).
-/
public theorem sytHookCount_add_eq_humpCount_sub (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n / 2) :
    (sytHookCount (n + 1) (2 * k - 1) : ℤ) + (sytHookCount n (2 * k - 1) : ℤ) =
      (motzkinHumpCount (n + 1) k : ℤ) - (motzkinHumpCount n k : ℤ) := by
  have tableaux := sytHookCount_add_eq_humpCount_sub.fromRow_add n 0 (2 * k - 1)
  have humps := sytHookCount_add_eq_humpCount_sub.humpCount_succ n k (by omega) hk
  rw [← sytHookCount_add_eq_humpCount_sub.syt_eq_fromRow,
    ← sytHookCount_add_eq_humpCount_sub.syt_eq_fromRow] at tableaux
  simp only [lt_irrefl, ite_false, add_zero, zero_add] at tableaux
  rw [ite_eq_right (by omega)] at tableaux
  omega

end

end MetaMathlibExt
