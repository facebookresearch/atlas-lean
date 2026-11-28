# Validity of linear inequalities in digraph homomorphism densities for tournaments is undecidable

No algorithm decides, given finite digraphs $D_1, \dots, D_k$ and rational coefficients $c_1, \dots, c_k$, whether $\sum_i c_i\, t(D_i, T) \ge 0$ holds for every tournament $T$.

A [tournament](../../../directed-graphs/tournaments-and-score-sequences/is-tournament.md) is an orientation of a complete graph. For a finite digraph $F$ and a finite tournament $T$, a *homomorphism* from $F$ to $T$ is a map $f \colon V(F) \to V(T)$ such that $(f(u), f(v))$ is an arc of $T$ for every arc $(u, v)$ of $F$, and the *homomorphism density* is

$$
t(F, T) = \frac{\hom(F, T)}{|V(T)|^{|V(F)|}} ,
$$

where $\hom(F, T)$ is the number of homomorphisms from $F$ to $T$. For a tournament with at least one vertex, $t(F, T)$ is the probability that a uniformly random map $V(F) \to V(T)$ is a homomorphism. For the tournament without vertices the quotient is read as for [graphs](../../../random-graphs/graph-limits/hom-density.md): $t(F, T) = 1$ if $F$ has no vertices and $t(F, T) = 0$ otherwise; admitting it adds only a condition on the coefficients of the digraphs without vertices and does not affect the theorem.

**Theorem (Chen, Lin, Ma and Wei).** The following problem is undecidable.

- Instance: a positive integer $k$, finite digraphs $D_1, \dots, D_k$ and rational numbers $c_1, \dots, c_k$, each given by a signed integer numerator and a positive integer denominator.
- Question: does $\sum_{i=1}^{k} c_i\, t(D_i, T) \ge 0$ hold for all tournaments $T$?

The source states the theorem with real coefficients $c_1, \dots, c_k$. A machine needs a finite input, so the problem above takes rational coefficients; its undecidability follows from the source's proof, whose hard instances, built in Lemmas 3.4 to 3.6 from polynomials with integer coefficients by clearing the density denominators and writing products of densities as densities of disjoint unions, have integer coefficients. Since products of densities are densities of disjoint unions, polynomial inequalities in digraph homomorphism densities for tournaments are covered as well. This is the tournament analogue of the [graph case](validity-of-linear-homomorphism-density-inequal.md) and of the [kernel case](validity-of-kernel-homomorphism-density-inequal.md).

## Depends on

- [Tournament](../../../directed-graphs/tournaments-and-score-sequences/is-tournament.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof reduces Hilbert's tenth problem, in the form that it is undecidable whether a polynomial $p(x_1, \dots, x_s)$ with integer coefficients, $s \ge 6$, is negative at some point of $\{1/n : n \ge 1\}^s$ (Lemma 3.1 of the version read, taken from Blekherman, Raymond and Wei). For each such $p$ it builds a quantum digraph $f(p)$ whose density is negative for some tournament exactly when $p$ is negative at such a point. Since cycle densities in tournaments are not power sums of real numbers in general, the construction uses a symmetrization trick: specific digraphs whose densities in every tournament are power sums of real numbers. Hilbert's tenth problem enters through the linked theorem of Davis, Putnam, Robinson and Matiyasevich. A good expansion links pages for Lemma 3.1, for the symmetrization construction and for the main Lemma 3.3 on the extremal ratios of necklace densities, which have none on main.

## Sources

- H. Chen, Y. Lin, J. Ma and F. Wei, "Undecidability of polynomial inequalities in tournaments", *International Mathematics Research Notices* 2025(11), article rnaf131, 2025, doi:10.1093/imrn/rnaf131; read in arXiv:2412.04972v2: Theorem 1.4 (the undecidability statement), the definitions of tournaments, digraph homomorphisms and densities in Section 1, Theorem 2.1 (Matiyasevich) in Section 2, Lemma 3.1, the main Lemma 3.3 and Lemmas 3.4 to 3.6 with the reduction in Section 3, and the construction of Section 4, in the numbering of that version.
