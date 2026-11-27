# Validity of linear inequalities in kernel homomorphism densities is undecidable

For every class of kernels that contains all kernels with values in $\{0, 1\}$, such as all kernels, all graphons, or the kernels bounded by $a > 0$ in absolute value, no algorithm decides whether a given linear combination of homomorphism densities is nonnegative on the whole class.

A *kernel* is a bounded symmetric measurable function $W \colon [0,1]^2 \to \mathbb{R}$. Let $\mathcal{W}$ be the set of kernels, $\mathcal{W}_0$ the set of [graphons](../../../random-graphs/finitely-forcible-graphons/is-graphon.md) (kernels with values in $[0,1]$), and, for $a > 0$, $\mathcal{W}_a$ the set of kernels with $\|W\|_\infty \le a$. For a finite simple graph $H$ on $\{1, \dots, k\}$ and a kernel $W$, the [homomorphism density](../../../random-graphs/graph-limits/graphon-hom-density.md) is

$$
t(H, W) = \int_{[0,1]^k} \prod_{ij \in E(H)} W(x_i, x_j) \, dx_1 \cdots dx_k .
$$

**Theorem (Blekherman, Raymond and Wei).** Let $\mathcal{W}^*$ be any set of kernels that contains every kernel with range $\{0, 1\}$. The following problem is undecidable.

- Instance: a positive integer $k$, finite graphs $H_1, \dots, H_k$ and real numbers $c_1, \dots, c_k$.
- Question: does $\sum_{i=1}^{k} c_i\, t(H_i, W) \ge 0$ hold for all $W \in \mathcal{W}^*$?

In particular this holds for $\mathcal{W}^* = \mathcal{W}$, $\mathcal{W}_0$ and $\mathcal{W}_a$ for every $a > 0$. As an algorithmic input the coefficients are given exactly, for instance as rational numbers, as in the source's discussion of certificates for quantum graphs with rational coefficients.

The case $\mathcal{W}^* = \mathcal{W}_0$ is the graphon form of the [theorem of Hatami and Norine](validity-of-linear-homomorphism-density-inequal.md) for finite graphs, which the source generalizes to kernels taking negative values. Products of densities are densities of disjoint unions, so polynomial inequalities are covered as well. The source also derives that some quantum graph nonnegative on $\mathcal{W}$ (or $\mathcal{W}_1$) admits no certificate $gf = h$ with sums of squares $g, h$, answering a question of Lovász for kernels.

## Depends on

- [Finite simple graph](../../../planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Graphon](../../../random-graphs/finitely-forcible-graphons/is-graphon.md)
- [Homomorphism density in a graphon](../../../random-graphs/graph-limits/graphon-hom-density.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

As for graphs, the proof reduces Hilbert's tenth problem: it is undecidable whether a polynomial with integer coefficients takes a negative value at some point of $\{1/n : n \in \mathbb{N}\}^{\ell - 1}$, $\ell \ge 7$ (Lemma 2.21 of the version read). For each such polynomial the source constructs a quantum graph whose density is negative for some kernel of $\mathcal{W}^*$ exactly when the polynomial is negative at such a point; the construction forces the extremal values to occur at kernels with range $\{0, 1\}$ and controls kernels with negative values. A good expansion links that lemma and the undecidability of Hilbert's tenth problem, which have no pages.

## Sources

- G. Blekherman, A. Raymond and F. Wei, "Undecidability of polynomial inequalities in weighted graph homomorphism densities", *Forum of Mathematics, Sigma* 12, article e40, 2024, doi:10.1017/fms.2024.19; read in arXiv:2207.12378v1: Theorem 1.3 (the undecidability statement), Corollary 1.4, the definitions of $\mathcal{W}$, $\mathcal{W}_0$ and $\mathcal{W}_a$ in Section 1, and Lemma 2.21 with the reduction from Hilbert's tenth problem, in the numbering of that version.
