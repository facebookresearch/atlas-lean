/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Shadow Markoff trees

In the tree rooted at $(1 + ε, 1 + ε, 1 + ε)$, the shadow part of each triple equals
its classical part. This follows Nathan Bonin, *Conditions of Positivity on a Shadow
Markoff Tree*.

A solution `(A, B, C) = (a + αε, b + βε, c + γε)` of the shadow Markoff equation
`A² + B² + C² = (3 - σε) ABC` (`ε² = 0`) is stored as the pair `(x, y)` of its classical part
`x = (a, b, c)` and its shadow part `y = (α, β, γ)`. The tree starts with the root and the
mutations at positions `0` and `1` in succession, followed by every non-backtracking sequence
of mutations.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Shadow Markoff mutation.** A state is a pair $(x, y)$ of a classical part
$x \in \mathbb{Q}^3$ and a shadow part $y \in \mathbb{Q}^3$, with coordinates indexed by the
positions $0, 1, 2$. The shadow Markoff mutation at position $i$ replaces $x_i$ by
$x_i' = \bigl(\sum_{j \ne i} x_j^2\bigr) / x_i$ and $y_i$ by
$\bigl(-x_i' y_i + 2 \sum_{j \ne i} x_j y_j\bigr) / x_i$, and leaves every other coordinate of
$x$ and $y$ unchanged.

Division by $0$ gives $0$: if $x_i = 0$, the new $x_i$ and the new $y_i$ are both $0$.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Section 1, equations (MutA) and (SMarmutBis). -/
def shadowMarkoffMutate (i : Fin 3) (s : (Fin 3 → ℚ) × (Fin 3 → ℚ)) :
    (Fin 3 → ℚ) × (Fin 3 → ℚ) :=
  let x' : ℚ := (∑ j ∈ Finset.univ.erase i, s.1 j ^ 2) / s.1 i
  (Function.update s.1 i x',
    Function.update s.2 i ((-x' * s.2 i + 2 * ∑ j ∈ Finset.univ.erase i, s.1 j * s.2 j) / s.1 i))

/-- **Initial triple of a shadow Markoff tree.** For
$v = (\alpha, \beta, \gamma) \in \mathbb{Z}^3$, the initial triple with shadow part $v$ is
$(1 + \alpha\varepsilon, 1 + \beta\varepsilon, 1 + \gamma\varepsilon)$, where
$\varepsilon^2 = 0$. It is stored as the state $(x, y)$ with classical part
$x = (1, 1, 1) \in \mathbb{Q}^3$ and shadow part
$y = (\alpha, \beta, \gamma) \in \mathbb{Q}^3$.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Section 1, equation (InitTrip). -/
def shadowMarkoffRoot (v : Fin 3 → ℤ) : (Fin 3 → ℚ) × (Fin 3 → ℚ) :=
  (fun _ => 1, fun i => (v i : ℚ))

/-- **Lower nodes of a shadow Markoff tree.** Fix $v \in \mathbb{Z}^3$ and let $r$ be the
initial triple with shadow part $v$, viewed as a state (a pair of a classical part and a shadow
part, both in $\mathbb{Q}^3$, with coordinates indexed by the positions $0, 1, 2$). The lower
nodes of the shadow Markoff tree of $v$ are pairs $(s, l)$ of a state $s$ and a position $l$, the
position mutated last. They are defined inductively: the state obtained from $r$ by the shadow
Markoff mutation at position $0$ and then at position $1$, tagged with $l = 1$, is a lower node;
and if $(s, l)$ is a lower node and $i \ne l$, then the mutation of $s$ at position $i$, tagged
with $i$, is a lower node. Nothing else is a lower node.

The first lower node has classical part $(2, 5, 1)$, the paper's $(1, 2, 5)$; the lower nodes
are the nodes of the tree below the paper's $(1, 1, 2)$.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Section 2 (the classical Markoff tree: "The initial triple
`(1,1,1)` is the root of the tree. It is followed by `(1,1,2)` and `(1,2,5)`. After that, any
mutation is allowed.") and Section 4. -/
inductive ShadowMarkoffTreeNode (v : Fin 3 → ℤ) : (Fin 3 → ℚ) × (Fin 3 → ℚ) → Fin 3 → Prop
  | start :
      ShadowMarkoffTreeNode v
        (shadowMarkoffMutate 1 (shadowMarkoffMutate 0 (shadowMarkoffRoot v))) 1
  | mutate {s : (Fin 3 → ℚ) × (Fin 3 → ℚ)} {l : Fin 3} (i : Fin 3) :
      ShadowMarkoffTreeNode v s l → i ≠ l → ShadowMarkoffTreeNode v (shadowMarkoffMutate i s) i

/-- **Shadow Markoff tree.** For $v \in \mathbb{Z}^3$, the shadow Markoff tree of $v$ is the
set of states $(x, y) \in \mathbb{Q}^3 \times \mathbb{Q}^3$ (classical part $x$, shadow part
$y$) consisting of the initial triple $r$ with shadow part $v$, the shadow Markoff mutation of
$r$ at position $0$, and the state $s$ of every lower node $(s, l)$ of the shadow Markoff tree
of $v$.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Sections 2 and 4. -/
def shadowMarkoffTree (v : Fin 3 → ℤ) : Set ((Fin 3 → ℚ) × (Fin 3 → ℚ)) :=
  {shadowMarkoffRoot v, shadowMarkoffMutate 0 (shadowMarkoffRoot v)} ∪
    {s | ∃ l, ShadowMarkoffTreeNode v s l}

/-- **The first two mutations in the tree of the vertex $(0:0:1)$.** Number the positions
$0, 1, 2$ and write a state as $(x \mid y)$, with classical part $x \in \mathbb{Q}^3$ and shadow
part $y \in \mathbb{Q}^3$. The initial triple $(1, 1, 1 + \varepsilon)$, where
$\varepsilon^2 = 0$, has shadow part $(0, 0, 1)$ (the paper's vertex $(0:0:1)$) and is the state
$(1, 1, 1 \mid 0, 0, 1)$. Its shadow Markoff mutation at position $0$ is
$(2, 1, 1 \mid 2, 0, 1)$, and the mutation of that state at position $1$ is
$(2, 5, 1 \mid 2, 10, 1)$.

These match the labels $2\ 2$ and $5\ 10$ of the paper's figure.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Section 4.1 (the tree of the vertex `(0:0:1)`). -/
theorem shadowMarkoffMutate_vertex_001 :
    shadowMarkoffMutate 0 (shadowMarkoffRoot ![0, 0, 1]) = (![2, 1, 1], ![2, 0, 1]) ∧
      shadowMarkoffMutate 1 (shadowMarkoffMutate 0 (shadowMarkoffRoot ![0, 0, 1])) =
        (![2, 5, 1], ![2, 10, 1]) := by
  have h0 : shadowMarkoffMutate 0 (shadowMarkoffRoot ![0, 0, 1]) = (![2, 1, 1], ![2, 0, 1]) := by
    ext i <;> fin_cases i <;>
      simp [shadowMarkoffMutate, shadowMarkoffRoot, Function.update, Finset.sum_erase_eq_sub,
        Fin.sum_univ_three]
  refine ⟨h0, ?_⟩
  rw [h0]
  ext i <;> fin_cases i <;>
    simp [shadowMarkoffMutate, Function.update, Finset.sum_erase_eq_sub, Fin.sum_univ_three] <;>
    norm_num

/-- **Shadow parts equal classical parts when $v = (1, 1, 1)$.** In the shadow Markoff tree of
$v = (1, 1, 1)$, the tree of the initial triple
$(1 + \varepsilon, 1 + \varepsilon, 1 + \varepsilon)$ with $\varepsilon^2 = 0$, every solution
$(x, y)$ has shadow part $y$ equal to its classical part $x$.

So the shadow parts of this tree reproduce the classical Markoff tree.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Lemma 3 (`jis-2024-24.8.3-lem-3`). -/
theorem shadowMarkoffTree_one_shadow_eq :
    ∀ s ∈ shadowMarkoffTree (fun _ => 1), s.2 = s.1 := by
  have mutate (i : Fin 3) {s : (Fin 3 → ℚ) × (Fin 3 → ℚ)} (h : s.2 = s.1) :
      (shadowMarkoffMutate i s).2 = (shadowMarkoffMutate i s).1 := by
    by_cases hi : s.1 i = 0
    · simp [shadowMarkoffMutate, h, hi]
    · simp only [shadowMarkoffMutate, h, pow_two, neg_mul, div_mul_cancel₀ _ hi, two_mul,
        neg_add_cancel_left]
  have root : (shadowMarkoffRoot (fun _ => 1)).2 = (shadowMarkoffRoot (fun _ => 1)).1 := rfl
  intro s hs
  rcases hs with (rfl | rfl) | ⟨l, node⟩
  · exact root
  · exact mutate 0 root
  · induction node with
    | start => exact mutate 1 (mutate 0 root)
    | mutate i _ _ ih => exact mutate i ih

end

end MetaMathlibExt
