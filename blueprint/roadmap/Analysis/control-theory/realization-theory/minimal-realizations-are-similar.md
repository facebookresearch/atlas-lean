# Minimal realizations are unique up to a unique similarity

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $(A_1, B_1, C_1)$ and $(A_2, B_2, C_2)$ be **minimal** realizations of the same Markov sequence $\mathcal{A}$ in $\mathbb{K}^{p \times m}$, in the sense of [minimal realizations](minimal-realizations-are-canonical.md). Then both have the same dimension $n$, and there is a **unique** invertible $T \in \mathbb{K}^{n \times n}$ with

$$T A_1 = A_2 T, \qquad T B_1 = B_2, \qquad C_1 = C_2 T .$$

Conversely, triples related in this way realize the same Markov sequence. In particular the only such $T$ relating a minimal realization to itself is the identity. For $n = 0$ both triples are empty and $T$ is the empty $0 \times 0$ matrix.

Sontag's proof: both triples are canonical, so with $R_i = R(A_i, B_i)$ and $O_i = O(A_i, C_i)$ the identities $O_1 R_1 = O_2 R_2$, $O_1 A_1 R_1 = O_2 A_2 R_2$, $O_1 B_1 = O_2 B_2$ and $C_1 R_1 = C_2 R_2$ hold; with a right inverse $R_1^{\#}$ of $R_1$ and a left inverse $O_2^{\#}$ of $O_2$ (empty matrices when $n = 0$, by the conventions for $R_0$ and $O_0$), the matrix $T = R_2 R_1^{\#} = O_2^{\#} O_1$ is invertible and intertwines the triples. Any $T$ with $T B_1 = B_2$ and $T A_1 = A_2 T$ satisfies $T A_1^{i} B_1 = A_2^{i} B_2$ for all $i$, hence $T R_1 = R_2$ and $T = R_2 R_1^{\#}$, which gives uniqueness.

## Depends on

- [Minimal realizations are exactly the canonical ones](minimal-realizations-are-canonical.md): the notions of realization and minimality.

## Proof depends on

- [Minimal realizations are exactly the canonical ones](minimal-realizations-are-canonical.md): minimal realizations are canonical and of equal dimension.
- [Hankel factorization of Markov parameters](hankel-factorization-of-markov-parameters.md): the four identities between the two triples.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 6.5: Definition 6.5.8, Theorem 27, part 3, with its proof, and Remark 6.5.10 (pp. 286–287). Sontag writes the similarity as $T^{-1} A T = \tilde A$; the $T$ above is its inverse.
