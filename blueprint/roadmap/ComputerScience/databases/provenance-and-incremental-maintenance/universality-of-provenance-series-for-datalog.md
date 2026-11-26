# Universality of provenance series for Datalog

Let $X$ be the set of tuple identifiers of an input instance, and let $\mathbb N^\infty[[X]]$ be the semiring of formal
power series in the variables $X$ with coefficients in $\mathbb N^\infty$, which is commutative and
$\omega$-continuous (the Datalog provenance semiring). Tag each input tuple with its own identifier. For every
commutative $\omega$-continuous semiring $K$ and every valuation $v : X \to K$ there is a unique
$\omega$-continuous semiring homomorphism $\mathrm{Eval}_v : \mathbb N^\infty[[X]] \to K$ extending $v$, and for
every Datalog query $q$, evaluating $q$ on the $K$-relation obtained by applying $v$ to the tags equals
$\mathrm{Eval}_v$ applied to the tags of $q$ evaluated on the identifier-tagged instance. So Datalog on $K$-relations
factors through provenance series, as positive relational algebra factors through provenance polynomials.

## Depends on

- [Datalog on K-relations over ω-continuous semirings](datalog-on-k-relations-over-omega-continuous-semirings.md)
- [Universality of provenance polynomials](universality-of-provenance-polynomials.md)

## Proof depends on

- [ω-continuous semiring homomorphisms commute with Datalog queries](omega-continuous-homomorphisms-commute-with-datalog.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Definition 6.1, Proposition 6.3 and Theorem 6.4. <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
