# The Diophantine problem is undecidable in metabelian groups of full-rank deficiency at least two

In a metabelian group given by a full-rank presentation in the variety of metabelian groups with at least two more generators than relators, no algorithm decides whether a finite system of equations has a solution.

Let $\mathcal{M}$ be the variety of metabelian groups and let $G = \langle A \mid R \rangle_{\mathcal{M}} = \langle a_1, \dots, a_n \mid r_1, \dots, r_m \rangle_{\mathcal{M}}$ be a finite presentation in $\mathcal{M}$. Its relation matrix $M(A, R)$ is the $m \times n$ integer matrix whose $(i, j)$ entry is the exponent sum of $a_j$ in $r_i$, and the presentation has *full rank* if $M(A, R)$ has rank $\min(m, n)$. The *Diophantine problem* $\mathcal{D}(G)$ asks, given a finite system of equations with constants from $G$, whether it has a solution in $G$.

**Theorem (Garreta, Legarreta, Miasnikov and Ovchinnikov).** Let $G = \langle A \mid R \rangle_{\mathcal{M}}$ be a metabelian group given by a full-rank presentation (Theorem 1.3 of arXiv:2006.06371v1).

1. If $|R| \le |A| - 2$, then the ring $\mathbb{Z}$ is interpretable in $G$ by finite systems of equations, and $\mathcal{D}(G)$ is undecidable.
2. If $|R| \ge |A|$, then $\mathcal{D}(G)$ is decidable; in fact the first-order theory of $G$ is decidable.

The case of deficiency one, $|R| = |A| - 1$, is left open in the source; there, some presentations define groups with decidable Diophantine problem, such as cyclic groups and $BS(1, n)$. The source also shows that random metabelian groups in the few-relators model with all relators of length $\ell$ satisfy clause 1 asymptotically almost surely as $\ell \to \infty$ when $m \le n - 2$ (Theorem 4.2). The nilpotent analogue is [the undecidability of the Diophantine problem in full-rank nilpotent groups](diophantine-problem-in-full-rank-nilpotent-groups.md).

## Depends on

- [Group](../../group-basics/group.md)
- [Metabelian groups](../../geometric-group-theory/permutation-stability/metabelian.md)

## Proof depends on

- [The Diophantine problem is undecidable in nilpotent groups of full-rank deficiency at least two](diophantine-problem-in-full-rank-nilpotent-groups.md)

## Expansion

For clause 1, the 2-nilpotent quotient $G/\gamma_3(G)$ has the presentation $\langle A \mid R \rangle_{\mathcal{N}_2}$, again of full rank and deficiency at least two, so $\mathbb{Z}$ is interpretable by equations in $G/\gamma_3(G)$ by the nilpotent result (Theorem 3.8 of arXiv:2006.06371v1, quoting Garreta, Miasnikov and Ovchinnikov). In a finitely generated metabelian group every verbal subgroup has finite width, so $\gamma_3(G)$ is definable by equations and $G/\gamma_3(G)$ is interpretable in $G$ (Proposition 3.9); by transitivity $\mathbb{Z}$ is interpretable in $G$, and the undecidability of $\mathcal{D}(\mathbb{Z})$ gives clause 1. For clause 2, $G$ is virtually abelian by the structure theorem for full-rank metabelian presentations (Theorem 1.1), and the Diophantine problem of a finitely generated virtually abelian group is decidable (Ershov). A good expansion links the finite width of verbal subgroups of finitely generated metabelian groups (Romankov) and Ershov's decidability theorem for virtually abelian groups, which have no pages.

## Sources

- A. Garreta, L. Legarreta, A. Miasnikov and D. Ovchinnikov, "Metabelian groups: full-rank presentations, randomness and Diophantine problems", *Journal of Group Theory* 24 (2021), no. 3, 453–466, doi:10.1515/jgth-2020-0091; read as arXiv:2006.06371v1, <https://arxiv.org/abs/2006.06371v1>: Theorems 1.1, 1.3, 3.8 and 4.2, Proposition 3.9, Remark 1.4 and the proof of Theorem 1.3 in Section 3, in the numbering of arXiv:2006.06371v1.
