# Validity of linear inequalities between graph homomorphism densities is undecidable

No algorithm decides, given finite graphs $H_1, \dots, H_k$ and integers $a_1, \dots, a_k$, whether $a_1 t(H_1; G) + \dots + a_k t(H_k; G) \ge 0$ holds for every finite graph $G$.

For finite simple graphs $H$ and $G$, the [homomorphism density](../../../random-graphs/graph-limits/hom-density.md) $t(H; G)$ is, when $G$ has at least one vertex, the probability that a uniformly random map $V(H) \to V(G)$ sends every edge of $H$ to an edge of $G$; equivalently $t(H; G) = \hom(H; G) / |V(G)|^{|V(H)|}$, where $\hom(H; G)$ is the number of homomorphisms from $H$ to $G$ ([homomorphism densities count homomorphisms](../../../random-graphs/graph-limits/hom-density-adj-weight.md)). For the graph without vertices the linked definition reads $t(H; G)$ as $1$ if $H$ has no vertices and as $0$ otherwise; admitting it adds only a condition on the coefficients of the graphs without vertices and does not affect the theorem.

**Theorem (Hatami and Norine).** The following problem is undecidable.

- Instance: a positive integer $k$, finite graphs $H_1, \dots, H_k$ and integers $a_1, \dots, a_k$.
- Question: does the inequality

$$
a_1 t(H_1; G) + \dots + a_k t(H_k; G) \ge 0
$$

hold for every graph $G$?

(Theorem 2.12 of the source.)

Since products of homomorphism densities are densities of disjoint unions, the same holds for polynomial inequalities in homomorphism densities, and, as the source notes, the analogous problem for linear inequalities in the homomorphism numbers $\hom(H_i; G)$ (observed earlier by Kopparty and Rossman, following Ioannidis and Ramakrishnan) is also undecidable. In contrast, positivity of a polynomial with rational coefficients on real arguments is decidable by Tarski's theorem.

## Depends on

- [Finite simple graph](../../../planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Homomorphism density](../../../random-graphs/graph-limits/hom-density.md)
- [Edge weight of a simple graph](../../../random-graphs/graph-limits/adj-weight.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

By Matiyasevich's solution of Hilbert's tenth problem, it is undecidable whether a polynomial with integer coefficients is nonnegative at all positive integers; substituting $y_i = 1/(1 - x_i)$ turns this into the undecidable question whether a polynomial $p(x_1, \dots, x_k)$ with integer coefficients, $k \ge 6$, takes a negative value on the set $\{1 - 1/n : n \in \mathbb{N}\}^k$ (Lemma 5.1 of the version read). The key observation is that relations between densities of different graphs can be tight only on a sparse set of values: by Bollobás's sharpening of Goodman's bound $t(K_3; G) \ge g(t(K_2; G))$, $g(x) = 2x^2 - x$, if $t(K_2; G) \in [1 - 1/t, 1 - 1/(t+1)]$ then $t(K_3; G) \ge L(t(K_2; G))$, where $L$ is the linear interpolation of $g$ between the endpoints (Theorem 5.2). Since $L > g$ inside each such interval, $t(K_3; G) = g(t(K_2; G))$ is possible only when $t(K_2; G)$ is one of the points $1 - 1/n$; equality with $L$ itself can occur elsewhere (the graph on three vertices with one edge has $t(K_2) = 2/9$ and $t(K_3) = 0 = L(2/9)$). The proof builds a quantum graph whose density is negative for some graph exactly when $p$ is negative somewhere on that set. Hilbert's tenth problem enters through the linked theorem of Davis, Putnam, Robinson and Matiyasevich. A good expansion links pages for Bollobás's theorem on the edge and triangle densities and for the lemma reducing Hilbert's tenth problem to the set $\{1 - 1/n\}$, which have none on main.

## Sources

- H. Hatami and S. Norine, "Undecidability of linear inequalities in graph homomorphism densities", *Journal of the American Mathematical Society* 24(2):547–565, 2011, doi:10.1090/S0894-0347-2010-00687-X; read in arXiv:1005.2382v3: Theorem 2.12 (the undecidability statement) and the remark after it on homomorphism numbers, Lemma 5.1 and Theorem 5.2 (Bollobás) in Section 5 (Undecidability), in the numbering of that version.
