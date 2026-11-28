# Closed semilinear separating invariants for nine 3×3 matrices are undecidable

The semilinear invariant problem is undecidable already for instances with exactly nine matrices of dimension $3$ when the separating invariant is required to be topologically closed. The proof encodes the infinite Post correspondence problem with nine pairs.

**Theorem (Fijalkow, Lefaucheux, Ohlmann, Ouaknine, Pouly and Worrell).** The following problem is undecidable: given nine matrices $A_1, \dots, A_9 \in \mathbb{A}^{3 \times 3}$ and points $x, y \in \mathbb{A}^3$ (algebraic entries), does there exist a closed semilinear set $\mathcal{I}$ with $x \in \mathcal{I}$, $A_i \mathcal{I} \subseteq \mathcal{I}$ for $i = 1, \dots, 9$, and $y \notin \mathcal{I}$?

The number of matrices ($9$) and the dimension ($3$) are fixed; only the entries of the matrices and points vary. The same paper trades matrices for dimension: the closed problem stays undecidable for two matrices of dimension $27$ (its Theorem 9).

## Depends on

- [Semilinear invariant problem](semilinear-invariant-problem.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [König's lemma for finitely branching graphs](../../../../concurrent-systems-and-protocols/petri-nets/decision-procedures/konig-s-lemma-for-finitely-branching-graphs.md)

## Expansion

Start from an instance $\{(u^{(i)}, v^{(i)}) : 1 \le i \le 9\}$ of the infinite Post correspondence problem, which asks for an infinite word $w$ over $\{1, \dots, 9\}$ with $u^{(w_1)} u^{(w_2)} \cdots = v^{(w_1)} v^{(w_2)} \cdots$; Halava and Harju proved it undecidable for nine pairs. After recoding the words over $\{0, 2\}$, encode a word $w$ by its quaternary value $[w] = \sum_i w_i 4^{1-i} \in [0, 8/3]$. The reduction uses the rational matrices

$$
M_i = \begin{bmatrix} 1 & [u^{(i)}] & -[v^{(i)}] \\ 0 & 4^{-|u^{(i)}|} & 0 \\ 0 & 0 & 4^{-|v^{(i)}|} \end{bmatrix}, \qquad x = (0, 1, 1), \quad y = (0, 0, 0),
$$

so that a product along a finite word $w$ sends $x$ to $([u^{(w)}] - [v^{(w)}], 4^{-|u^{(w)}|}, 4^{-|v^{(w)}|})$. If the instance has an infinite solution, the images of $x$ along its prefixes converge to $y$, so every closed invariant containing $x$ contains $y$. If it has none, König's lemma gives a bound $n_0$ such that every infinite word shows a mismatch within the first $n_0$ letters, and the union of the finitely many images of $x$ along words of length at most $n_0 + 1$ with the closed semilinear set $\{(s, c, d) : |s| \ge 4(c + d) + 4^{-n_0-1},\ c \ge 0,\ d \ge 0\}$ is a separating invariant. A good expansion links a page for the undecidability of the infinite Post correspondence problem for nine pairs (Halava and Harju).

## Sources

- Nathanaël Fijalkow, Engel Lefaucheux, Pierre Ohlmann, Joël Ouaknine, Amaury Pouly and James Worrell, "On the Monniaux Problem in Abstract Interpretation", Static Analysis (SAS 2019), Lecture Notes in Computer Science 11822, pp. 162–180, 2019, <https://doi.org/10.1007/978-3-030-32304-2_9>; Theorem 8, Theorem 9 and the proof of Theorem 8 in Section 4 of arXiv:1907.08257v1, <https://arxiv.org/abs/1907.08257v1>.
