# A unit-rule cycle in a derivation makes a Datalog provenance coefficient infinite

In the setting of [Universality of provenance series for Datalog](universality-of-provenance-series-for-datalog.md),
let $q$ be a Datalog query and $t$ a tuple in its result, and call a rule of the instantiation of $q$ a unit rule when
its body is a single intensional atom. If some derivation tree of $t$ contains a ground atom $s$ that lies on a cycle of
unit rules ($s$ is the head of one rule of the cycle and the body of another), then some coefficient of the provenance
series of $t$ is infinite, so the series is not in $\mathbb N[[X]]$: repeating the cycle at $s$ gives infinitely many
derivation trees of $t$ with the same leaves. This holds in particular when $t$ itself lies on such a cycle. The atom
on the cycle need not be $t$: with $E(a)$ tagged $X$, $M(a, b)$ tagged $Y$ and the rules $P(x) \mathrel{:-} E(x)$,
$P(x) \mathrel{:-} P(x)$ and $Q(y) \mathrel{:-} P(x), M(x, y)$, the tuple $Q(b)$ lies on no cycle of unit rules, yet the
coefficient of $XY$ in its series is infinite.

## Depends on

- [Universality of provenance series for Datalog](universality-of-provenance-series-for-datalog.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Definition 5.1 and Theorem 6.5 (whose stated equivalence holds only in the direction given here). <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
