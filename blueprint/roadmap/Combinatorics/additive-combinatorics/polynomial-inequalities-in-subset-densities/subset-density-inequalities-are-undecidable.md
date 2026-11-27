# Validity of polynomial inequalities in subset densities and additive energies is undecidable

No algorithm decides whether a given integer linear combination of densities of linear configurations, or a given integer polynomial in densities and additive energies, is nonnegative for every subset of every finite abelian group.

Let $G$ be a finite [abelian group](../../../GroupTheory/group-basics/abelian-group.md), written additively, and $A \subseteq G$; its *density* is $\alpha(A) = |A|/|G|$. For a *system of linear forms* $L = \{f_1(g_1, \dots, g_k), \dots, f_d(g_1, \dots, g_k)\}$, each $f_i$ an integer linear combination of the variables, let

$$
t(L, A) = \Pr\big[ f_1(g_1, \dots, g_k) \in A, \dots, f_d(g_1, \dots, g_k) \in A \big],
$$

where $(g_1, \dots, g_k) \in G^k$ is uniformly random; the source also admits negated forms $\neg f$, which require $f(g_1, \dots, g_k) \notin A$. A *quantum system of linear forms* is a formal product of such systems, with $t(L \cdot L', A) = t(L, A)\, t(L', A)$. Examples: $L = \{g\}$ gives $t(L, A) = \alpha(A)$, and $L = \{g, h, k, g + h - k\}$ gives the normalized *additive energy* $E(A)/|G|^3$, where $E(A)$ is the number of quadruples $(a_1, a_2, a_3, a_4) \in A^4$ with $a_1 + a_2 = a_3 + a_4$.

**Theorem (Li).**

1. It is undecidable, given positive integers $m, k$, quantum systems of linear forms $L_1, \dots, L_m$ in $k$ variables and integers $a_1, \dots, a_m$, whether $a_1 t(L_1, A) + \dots + a_m t(L_m, A) \ge 0$ for every subset $A \subseteq G$ of every finite abelian group $G$ (Theorem 1 of arXiv:2505.07378v1).
2. It is undecidable, given $k \ge 2$ and a polynomial $q \in \mathbb{Z}[x_1, \dots, x_k, y_1, \dots, y_k]$, whether $q(\alpha(A_1), \dots, \alpha(A_k), E(A_1), \dots, E(A_k)) \ge 0$ for all finite abelian groups $G_1, \dots, G_k$ and all subsets $A_i \subseteq G_i$ (Theorem 2 of arXiv:2505.07378v1), where, as in the proof of the source (Section 3), $E(A_i)$ denotes the normalized additive energy $E(A_i)/|G_i|^3$.

Many results of additive combinatorics, such as consequences of Kneser's theorem or the relation between small doubling and large additive energy, are inequalities of these kinds, so the theorem says that such inequalities cannot be established by a uniform algorithm. It parallels the theorem of Hatami and Norine that the validity of polynomial inequalities between graph homomorphism densities is undecidable.

## Depends on

- [Abelian group](../../../GroupTheory/group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof adapts the method of Hatami and Norine. For clause 1 the source starts from their result that nonnegativity of an integer polynomial on the region $R^k$ is undecidable, where $R = \{(x, y) \in [0, 1]^2 : y \ge h(x)\}$ is the region above Bollobás's lower bound $h$ for the triangle density in terms of the edge density (Lemma 3 of arXiv:2505.07378v1, a consequence of Lemmas 5.1 and 5.4 of Hatami and Norine), and constructs systems of linear forms in groups $\mathbb{Z}_{(k+1)^2}$ and their products whose densities realize the needed points of $R$ (Lemma 4). For clause 2 it uses that nonnegativity of an integer polynomial on $S^k$, with $S = \{1/n : n \in \mathbb{N}\}$, is undecidable by Matiyasevich's theorem (Lemma 6), together with the Fourier-analytic upper bound $E(A) \le \alpha^3 - \alpha^4 \{1/\alpha\}(1 - \{1/\alpha\})$ for the normalized energy (Lemma 5), which becomes $E(A) \le \alpha^3$ when $|A|$ divides $|G|$ and is attained by $A = \{0\} \subseteq \mathbb{Z}_n$. A good expansion links the Hatami–Norine undecidability of polynomial inequalities on $R^k$, which has no page on main or in this subject's run.

## Sources

- Y. Li and Y. Zhu, "Undecidability of polynomial inequalities in subset densities and additive energies", *Theoretical Computer Science* 1074 (2026), article 115911, doi:10.1016/j.tcs.2026.115911; read as arXiv:2505.07378v1, <https://arxiv.org/abs/2505.07378v1>, the first author's preprint of this paper: Theorems 1 and 2, Lemmas 3 to 6, the definitions of Section 1 and the normalization of the additive energy in Section 3, in the numbering of arXiv:2505.07378v1.
