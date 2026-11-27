# Datalog on Boolean-annotated relations is standard Datalog

For every Datalog query $q$ and every relation $R$ annotated in the Boolean semiring $\mathbb B = (\{\mathrm{false}, \mathrm{true}\}, \vee, \wedge, \mathrm{false}, \mathrm{true})$,
the support of $q(R)$ under the [Datalog semantics on $K$-relations](datalog-on-k-relations-over-omega-continuous-semirings.md)
equals the result of applying $q$, with the standard [Datalog semantics](../datalog/datalog-programs-and-the-immediate-consequence-operator.md),
to the ordinary relation $\mathrm{supp}(R)$.

## Depends on

- [Datalog on K-relations over ω-continuous semirings](datalog-on-k-relations-over-omega-continuous-semirings.md)
- [Datalog programs and the immediate consequence operator](../datalog/datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](../datalog/least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>, Proposition 5.4.
