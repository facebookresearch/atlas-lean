# Hilbert's tenth problem is undecidable over holomorphy rings of one-variable function fields of characteristic zero

Let $K$ be a function field in one variable over a field of characteristic zero, and $R$ a holomorphy ring of $K$ other than $K$ itself. If $K$ is countable and computable, Hilbert's tenth problem over $R$ is undecidable; in general it is undecidable for coefficients from a suitable finitely generated field.

Let $C$ be a field of characteristic $0$ and $K$ a function field in one variable over $C$, that is, a finite extension of the rational function field $C(t)$. A *prime* of $K$ is a nontrivial discrete valuation of $K$ trivial on $C$; let $\mathcal{P}_K$ be the set of primes, and for $\mathfrak{p} \in \mathcal{P}_K$ let $\mathcal{O}(\mathfrak{p})$ be its valuation ring. For a nonempty subset $\mathcal{W} \subseteq \mathcal{P}_K$, the ring

$$
\mathcal{O}_{K,\mathcal{W}} = \bigcap_{\mathfrak{p} \notin \mathcal{W}} \mathcal{O}(\mathfrak{p}) = \{ h \in K : \operatorname{ord}_{\mathfrak{p}} h \ge 0 \text{ for every } \mathfrak{p} \notin \mathcal{W} \}
$$

is a *holomorphy ring* of $K$; it equals $K$ exactly when $\mathcal{W} = \mathcal{P}_K$.

**Theorem (Moret-Bailly–Shlapentokh).**

1. Let $K$ be a countable computable function field in one variable of characteristic $0$. Then Hilbert's tenth problem is undecidable over every holomorphy ring of $K$ not equal to $K$.
2. Let $K$ be a function field in one variable of characteristic $0$ over a field of constants $C$. Then for every holomorphy ring $R$ of $K$ not equal to $K$ there are $x_1, \dots, x_n \in K \setminus C$ such that there is no algorithm that decides whether a polynomial equation with coefficients in $\mathbb{Q}(x_1, \dots, x_n)$ has a solution in $R$.

Conventions: the elements $x_1, \dots, x_n$ in clause 2 depend on $R$; clause 2 is needed because $K$ may be uncountable. The ring $R$ may contain primes of infinitely many degrees in its pole divisors; the case of rings of $\mathcal{S}$-integers, with $\mathcal{W}$ finite, had been treated earlier by Shlapentokh.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For function fields in one variable of characteristic zero, Moret-Bailly's work (see [Hilbert's tenth problem for function fields over real and p-adic fields](h10-for-function-fields-over-real-and-p-adic.md)) supplies the elliptic curves needed for a Diophantine model of $\mathbb{Z}$, but undecidability over the field itself also requires an existential definition of the order at a prime, which is not available in general. The source's main idea is that in a ring in which not all primes are inverted, the order at a prime can be defined, or nearly so, through divisibility. Combining this with Moret-Bailly's elliptic curves gives a Diophantine model of $\mathbb{Z}$ over every holomorphy ring other than $K$, and undecidability follows from the Davis–Putnam–Robinson–Matiyasevich theorem. When a set of constants containing $\mathbb{Z}$ is Diophantine over $K$, the same method gives an existential definition of $\mathbb{Z}$ over every holomorphy ring other than $K$ (Theorem 3 of the source). A good expansion links pages for Moret-Bailly's rank-one elliptic curves over function fields of characteristic zero, for the source's Theorem 3.2, which defines the order at a prime through divisibility, and for the transfer of undecidability along a Diophantine model.

## Sources

- Laurent Moret-Bailly and Alexandra Shlapentokh, *Diophantine undecidability of holomorphy rings of function fields of characteristic 0*, Ann. Inst. Fourier (Grenoble) 59 (2009), no. 5, 2103–2118, https://doi.org/10.5802/aif.2484, read in the copy arXiv:0805.3458v2: clauses 1 and 2 are Theorems 1 and 2 of its introduction, and holomorphy rings are defined in its Definition 3.1.
