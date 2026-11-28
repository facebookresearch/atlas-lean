# The lattice of effectively open subsets of ℝⁿ has the theory of arithmetic

For every n ≥ 1, the first-order theory of the lattice of effectively open subsets of ℝⁿ under inclusion is many-one equivalent to true first-order arithmetic; in particular it is undecidable.

**Theorem (Kudinov and Selivanov).** For a countably based space $X$ with a numbering $\beta$ of a base, a set is *effectively open* if it is $\bigcup\{\beta(a) \mid a \in W_n\}$ for a computably enumerable set $W_n$; for $\mathbb R^n$ the base consists of the open balls with rational centers and radii. Let $\Sigma^0_1(\mathbb R^n)$ be the lattice of effectively open subsets of $\mathbb R^n$ ordered by inclusion, and $\mathrm{FO}(\Sigma^0_1(\mathbb R^n))$ the set of first-order sentences in the signature $\{\subseteq\}$ true in it. For every $n \ge 1$,

$$
\mathrm{FO}(\Sigma^0_1(\mathbb R^n)) \equiv_m \mathrm{FO}(\mathbb N),
$$

where $\mathrm{FO}(\mathbb N)$ is the first-order theory of $(\mathbb N; +, \cdot)$ and $\equiv_m$ is many-one equivalence (Theorem 4.4 of the source).

More generally, the theory of the lattice of effectively open sets is *hereditarily undecidable* (every subtheory in its language is undecidable) for every strongly computable metric space, that is, a computable metric space with an infinite computable sequence of pairwise disjoint basic balls, and for every strongly computable $\varphi$-space (Theorem 4.1). By contrast, the theory of the lattice of all open subsets of $\mathbb R$ is decidable (Rabin).

## Depends on

- [Standard enumeration of the recursively enumerable sets](../../../../TheoryOfComputation/degrees-and-hierarchies/productive-creative-simple-and-immune-sets/enum-re.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

*Upper bound.* For an analytically representable locally compact space, inclusion between effectively open sets given by indices is an arithmetical relation, so the elementary diagram of the numbered lattice reduces to $\mathrm{FO}(\mathbb N)$ (Proposition 4.2).

*Lower bound.* Since the lattice is distributive, Boolean combinations and the constants $\emptyset$, $\mathbb R^n$ may be used. A point $x$ is computable iff $\mathbb R^n \setminus \{x\}$ is effectively open, so computable points are definable as complements of maximal proper effectively open sets. First-order formulas in $\subseteq$ define connectedness and connected components of effectively open sets (Corollary 4.5), and these are used to interpret $(\mathbb N; +, \cdot)$ in $\Sigma^0_1(\mathbb R^n)$. Theorem 4.1 is proved by interpreting, with two parameters, the lattice of computably enumerable sets, whose theory is hereditarily undecidable (Herrmann).

## Sources

- O. Kudinov and V. Selivanov, "First Order Theories of Some Lattices of Open Sets", *Logical Methods in Computer Science* 13(3), 2017, paper 16, pp. 1–18, <https://doi.org/10.23638/LMCS-13(3:16)2017>; read as arXiv:1705.04564v3, <https://arxiv.org/abs/1705.04564v3>: Section 2 (effectively open sets, strongly computable spaces), Theorem 4.1, Proposition 4.2, Lemma 4.3, Theorem 4.4 and Corollary 4.5.
