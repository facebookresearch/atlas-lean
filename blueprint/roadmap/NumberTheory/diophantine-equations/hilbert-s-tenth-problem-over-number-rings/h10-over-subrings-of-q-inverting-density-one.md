# Hilbert's tenth problem is undecidable over some subrings of the rationals inverting a set of primes of density one

There are disjoint computable sets of primes $\mathcal{T}_1$ and $\mathcal{T}_2$, both of natural density zero, such that for every set $\mathcal{S}$ of primes containing $\mathcal{T}_1$ and disjoint from $\mathcal{T}_2$, $\mathbb{Z}$ has a Diophantine model over $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$ and Hilbert's tenth problem over this ring is undecidable.

For a set $\mathcal{S}$ of prime numbers, let

$$
\mathcal{O}_{\mathbb{Q},\mathcal{S}} = \{ x \in \mathbb{Q} : \operatorname{ord}_p x \ge 0 \text{ for every prime } p \notin \mathcal{S} \},
$$

the ring of rational numbers whose denominators are divisible only by primes in $\mathcal{S}$; it is $\mathbb{Z}$ for $\mathcal{S} = \emptyset$ and $\mathbb{Q}$ when $\mathcal{S}$ contains every prime.

**Theorem (Poonen).** There exist computable sets of primes $\mathcal{T}_1$ and $\mathcal{T}_2$, both of natural density zero and with $\mathcal{T}_1 \cap \mathcal{T}_2 = \emptyset$, such that for every set $\mathcal{S}$ of primes with $\mathcal{T}_1 \subseteq \mathcal{S}$ and $\mathcal{S} \cap \mathcal{T}_2 = \emptyset$:

1. $\mathbb{Z}$ has a Diophantine model over $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$;
2. Hilbert's tenth problem over $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$ is undecidable.

Conventions: a Diophantine model of $\mathbb{Z}$ over a ring $R$ is a computable injection $\phi : \mathbb{Z} \to R^k$ (Definition 2.4 of the survey) whose image and the images of the graphs of addition and multiplication are Diophantine over $R$. Taking $\mathcal{S}$ to be the complement of $\mathcal{T}_2$ gives such rings in which the inverted primes have natural density one. Since $\mathcal{S}$ ranges over uncountably many sets, Hilbert's tenth problem over $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$ is meant for rings of algebraic numbers, as on the linked definition page: coefficients are rationals in $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$, written as fractions, with the promise that they lie in the ring.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)
- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Density of a set](../../additive-number-theory/natural-and-logarithmic-density/has-density.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Poonen models the integers by approximation. Fix an elliptic curve $E : y^2 = x^3 + ax + b$ of rank one over $\mathbb{Q}$ with generator $P$. The denominators of the coordinates of the multiples $nP$ form a divisibility sequence, and for large $n$ the point $nP$ has a primitive prime divisor; Poonen shows that the set of the largest primitive divisors $p_\ell$ of $\ell P$, for $\ell$ prime, has natural density zero. Forbidding these primes in denominators removes all multiples of $\ell P$ for unwanted $\ell$, and the choice can be arranged so that, apart from finitely many points, the only multiples of $P$ with coordinates in $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$ are $\pm \ell_j P = (x_{\ell_j}, \pm y_{\ell_j})$ with $|y_{\ell_j} - j| < 10^{-j}$. Then $j \mapsto y_{\ell_j}$ is a Diophantine model of the positive integers: $k = i + j$ exactly when $|y_{\ell_i} + y_{\ell_j} - y_{\ell_k}| < 1/3$, and $k = i^2$ exactly when $|y_{\ell_i}^2 - y_{\ell_k}| < 2/5$, both expressible with sums of squares, and multiplication follows from $xy = \tfrac12((x+y)^2 - x^2 - y^2)$. A Diophantine model of $\mathbb{Z}$ makes Hilbert's tenth problem over the ring undecidable by Matiyasevich's theorem. A good expansion links pages for the elliptic-curve facts used (divisibility of denominators, primitive divisors, and Poonen's density-zero theorem for the primes $p_\ell$, proved with results of Serre) and for the transfer of undecidability along a Diophantine model.

## Sources

- Bjorn Poonen, *Hilbert's tenth problem and Mazur's conjecture for large subrings of $\mathbb{Q}$*, J. Amer. Math. Soc. 16 (2003), no. 4, 981–990, https://doi.org/10.1090/S0894-0347-03-00433-8; the statement as recalled in Theorem 4.1 of the version of the survey below that was read.
- Alexandra Shlapentokh, *Defining integers*, Bull. Symbolic Logic 17 (2011), no. 2, 230–251, https://doi.org/10.2178/bsl/1305810912; the statement is Theorem 4.1 of arXiv:1008.0809v1, with the proof sketch of its Section 4.
