# Universality of provenance polynomials

Semiring homomorphisms commute with evaluation of positive relational algebra queries on $K$-relations.
Let $X$ be a set of variables and tag each tuple of an input instance with a distinct variable, giving an
$\mathbb{N}[X]$-instance $\bar{R}$. For every positive relational algebra query $q$, every commutative
semiring $K$ and every valuation $v : X \to K$, if $R$ is the $K$-instance obtained from $\bar{R}$ by
applying $v$ to the tags, then

$$q(R) = \mathrm{Eval}_v\big(q(\bar{R})\big),$$

where $\mathrm{Eval}_v : \mathbb{N}[X] \to K$ is the unique semiring homomorphism extending $v$.

## Depends on

- [K-relations and positive relational algebra over a semiring](k-relations-and-positive-relational-algebra-over-a-semiring.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Proposition 3.5, Proposition 4.2 and Theorem 4.3. <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
