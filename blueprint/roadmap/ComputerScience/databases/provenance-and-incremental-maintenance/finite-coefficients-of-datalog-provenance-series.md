# Datalog provenance series have finite coefficients exactly when no unit-rule cycle passes through the tuple

In the setting of [Universality of provenance series for Datalog](universality-of-provenance-series-for-datalog.md),
let $q$ be a Datalog query and $t$ a tuple in its result. The provenance series of $t$ lies in $\mathbb N[[X]]$ (every
coefficient finite) if and only if the instantiation of $q$ has no cycle of unit rules, rules whose body is a single
intensional atom, that passes through $t$ (with $t$ in the head of one of those unit rules and in the body of another).

## Depends on

- [Universality of provenance series for Datalog](universality-of-provenance-series-for-datalog.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Theorem 6.5. <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
