# Validity of linear inequalities in kernel homomorphism densities is undecidable

For every class of kernels that contains all kernels with values in $\{0, 1\}$, such as all kernels, all graphons, or the kernels bounded by $a \ge 1$ in absolute value, no algorithm decides whether a given linear combination of homomorphism densities with rational coefficients is nonnegative on the whole class; by rescaling, the same holds for the kernels bounded by any $a > 0$.

A *kernel* is a bounded symmetric measurable function $W \colon [0,1]^2 \to \mathbb{R}$. Let $\mathcal{W}$ be the set of kernels, $\mathcal{W}_0$ the set of [graphons](../../../random-graphs/finitely-forcible-graphons/is-graphon.md) (kernels with values in $[0,1]$), and, for $a > 0$, $\mathcal{W}_a$ the set of kernels with $\|W\|_\infty \le a$. For a finite simple graph $H$ on $\{1, \dots, k\}$ and a kernel $W$, the [homomorphism density](../../../random-graphs/graph-limits/graphon-hom-density.md) is

$$
t(H, W) = \int_{[0,1]^k} \prod_{ij \in E(H)} W(x_i, x_j) \, dx_1 \cdots dx_k .
$$

**Theorem (Blekherman, Raymond and Wei).** Let $\mathcal{W}^*$ be any set of kernels that contains every kernel with range $\{0, 1\}$. The following problem is undecidable.

- Instance: a positive integer $k$, finite graphs $H_1, \dots, H_k$ and rational numbers $c_1, \dots, c_k$, each given by a signed integer numerator and a positive integer denominator.
- Question: does $\sum_{i=1}^{k} c_i\, t(H_i, W) \ge 0$ hold for all $W \in \mathcal{W}^*$?

In particular this holds for $\mathcal{W}^* = \mathcal{W}$, $\mathcal{W}_0$ and $\mathcal{W}_a$ for every $a \ge 1$. It also holds for $\mathcal{W}_a$ with $0 < a < 1$, which does not contain every kernel with range $\{0, 1\}$ (the indicator of $[0, 1/2]^2$ has norm $1$): fix a rational $b$ with $0 < b \le a$; then $\mathcal{W}_a$ contains every kernel with range $\{0, b\}$, and since $t(H, bW) = b^{|E(H)|}\, t(H, W)$, the instance with coefficients $c_i$ for the kernels with range $\{0, 1\}$ becomes the instance with rational coefficients $c_i b^{-|E(H_i)|}$ for those with range $\{0, b\}$; the source states this rescaling just before its Theorem 1.3.

The source states the theorem with real coefficients $c_1, \dots, c_k$. A machine needs a finite input, so the problem above takes rational coefficients; its undecidability follows from the source's proof, whose hard instances, built in Lemmas 2.22 and 2.23 from polynomials with integer coefficients by clearing the density denominators and writing products of densities as densities of disjoint unions, have integer coefficients, and the source itself treats quantum graphs with rational coefficients as machine inputs in the proof of its Corollary 1.4.

The case $\mathcal{W}^* = \mathcal{W}_0$ is the graphon form of the [theorem of Hatami and Norine](validity-of-linear-homomorphism-density-inequal.md) for finite graphs, which the source generalizes to kernels taking negative values. Products of densities are densities of disjoint unions, so polynomial inequalities are covered as well. The source also derives that some quantum graph $f$ nonnegative on $\mathcal{W}$ (or $\mathcal{W}_1$) admits no certificate $gf = h$ in which $g$ is a nonzero sum of squares of labeled quantum graphs and $h$ is a sum of such squares (Corollary 1.4; with $g = h = 0$ the equation would hold for every $f$), and that the same argument rules out certificates $f + gf = h$ of Lovász's Problem 1.2 for kernels.

## Depends on

- [Finite simple graph](../../../planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Graphon](../../../random-graphs/finitely-forcible-graphons/is-graphon.md)
- [Homomorphism density in a graphon](../../../random-graphs/graph-limits/graphon-hom-density.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

As for graphs, the proof reduces Hilbert's tenth problem: it is undecidable whether a polynomial with integer coefficients takes a negative value at some point of $\{1/n : n \in \mathbb{N}\}^{\ell - 1}$, $\ell \ge 7$ (Lemma 2.21 of the version read). For each such polynomial the source constructs a quantum graph whose density is negative for some kernel of $\mathcal{W}^*$ exactly when the polynomial is negative at such a point; the ratios of necklace densities that enter the construction have the same convex hull for every class $\mathcal{W}^*$ (Theorem 1.5 of the version read, via Proposition 2.15), so kernels with negative values give no new negative values, and a negative witness, when there is one, can be chosen with range $\{0, 1\}$ (Lemma 2.24). Hilbert's tenth problem enters through the linked theorem of Davis, Putnam, Robinson and Matiyasevich. A good expansion links pages for Lemma 2.21, for the auxiliary polynomial of Lemma 2.22 and for the necklace profile theorem, which have none on main.

## Sources

- G. Blekherman, A. Raymond and F. Wei, "Undecidability of polynomial inequalities in weighted graph homomorphism densities", *Forum of Mathematics, Sigma* 12, article e40, 2024, doi:10.1017/fms.2024.19; read in arXiv:2207.12378v1: Theorem 1.3 (the undecidability statement) and the rescaling remark before it, Problem 1.2 and Corollary 1.4, the definitions of $\mathcal{W}$, $\mathcal{W}_0$ and $\mathcal{W}_a$ in Section 1, Theorem 1.5 and Proposition 2.15, and Lemmas 2.21 to 2.24 with the proof of Theorem 1.3 and of Corollary 1.4, in the numbering of that version.
