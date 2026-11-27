# Recursive asymptotic expansion of the two-locus sampling distribution

Consider two loci $A$ and $B$ with $K$ and $L$ alleles, finite-alleles mutation at each locus, and population-scaled recombination rate $\rho$. A two-locus sample configuration $(\mathbf a,\mathbf b,\mathbf c)$ records $a_i$ gametes typed only at $A$ (allele $i$), $b_j$ typed only at $B$, and $c_{ij}$ fully typed gametes with haplotype $(i,j)$; $\mathbf c_A = (c_{i\cdot})$, $\mathbf c_B = (c_{\cdot j})$ are the marginal counts and $c = \sum_{ij}c_{ij}$. Let $q(\mathbf a,\mathbf b,\mathbf c)$ be the stationary sampling probability and $q^A, q^B$ the one-locus sampling distributions. As $\rho \to \infty$,

$$
q(\mathbf a,\mathbf b,\mathbf c) = q_0(\mathbf a,\mathbf b,\mathbf c) + \frac{q_1(\mathbf a,\mathbf b,\mathbf c)}{\rho} + \frac{q_2(\mathbf a,\mathbf b,\mathbf c)}{\rho^2} + \cdots,
$$

with coefficients independent of $\rho$.

**Theorem.**

1. (Leading terms.) $q_0(\mathbf a,\mathbf b,\mathbf c) = q^A(\mathbf a + \mathbf c_A)\,q^B(\mathbf b + \mathbf c_B)$ (the loci are independent at infinite recombination), and, with $\mathbf e_i$ the $i$-th unit vector,

$$
\begin{aligned}
q_1 &= \binom{c}{2} q^A(\mathbf a + \mathbf c_A)\,q^B(\mathbf b + \mathbf c_B) - q^B(\mathbf b + \mathbf c_B)\sum_{i}\binom{c_{i\cdot}}{2} q^A(\mathbf a + \mathbf c_A - \mathbf e_i)\\
&\quad - q^A(\mathbf a + \mathbf c_A)\sum_{j}\binom{c_{\cdot j}}{2} q^B(\mathbf b + \mathbf c_B - \mathbf e_j) + \sum_{i,j}\binom{c_{ij}}{2} q^A(\mathbf a + \mathbf c_A - \mathbf e_i)\,q^B(\mathbf b + \mathbf c_B - \mathbf e_j).
\end{aligned}
$$

2. (Arbitrary order.) Writing $q_M$ as a sum of terms $g_u^{(m)}(\mathbf a,\mathbf b,\mathbf r)$ indexed by levels $\ell = m + u$, one has $g_0^{(0)}(\mathbf a,\mathbf b,\mathbf 0) = q^A(\mathbf a)q^B(\mathbf b)$; for $m > 0$ each $g_u^{(m)}$ on level $\ell$ is an explicit combination of at most four entries $g_u^{(m-2)}, g_{u-1}^{(m-1)}, g_{u-2}^{(m)}, g_{u-3}^{(m+1)}$ on level $\ell - 2$; and for $m = 0$, $g_u^{(0)}$ is determined by $g_{u-1}^{(1)}$ and by terms with smaller configurations on the same level. Every term with $m + u$ odd vanishes.
3. (Selection.) If locus $A$ is under selection and $B$ is neutral, the same zeroth- and first-order formulas hold with $q^A$ replaced by the one-locus sampling distribution under selection.

So all coefficients $q_M$ are computable by a finite recursion from one-locus sampling distributions.

## Expansion

The sampling distribution satisfies a coalescent-with-recombination recursion in which recombination acts on fully typed gametes at rate proportional to $\rho$. Substituting the expansion and matching powers of $1/\rho$ gives equations whose leading part forces the loci to decouple. Reorganizing $q_M$ by the number of remaining fully typed pairs $m$ and an auxiliary index $u$ turns the recursion into a triangular scheme that can be automated; the parity statement follows because each step of the recursion changes the level by two.

## Sources

- Paul A. Jenkins, Yun S. Song, "Padé approximants and exact two-locus sampling distributions", *The Annals of Applied Probability* 22 (2012), 576–607, <https://doi.org/10.1214/11-AAP780>; preprint arXiv:1107.3897, <https://doi.org/10.48550/arXiv.1107.3897>. Numbering of the arXiv version: Section 2 (Theorem 2.1, from earlier work of the same authors), Section 3 (Theorem 3.1, Corollary 3.1), Section 5 (Theorem 5.1).
