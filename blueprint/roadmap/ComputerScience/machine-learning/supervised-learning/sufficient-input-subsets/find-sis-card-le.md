# FindSIS returns the smallest sufficient set of the chain

**Proposition 1 (second part)** of Carter et al.: let $g$ be a real function on the finite
subsets of a set of features, $\tau \in \mathbb{R}$ a threshold and $\pi$ any rule choosing an
element of every nonempty finite set. If [FindSIS](find-sis.md) returns $S$ from a finite set $R$,
then every set $T$ of the [backward-selection chain](chain.md) from $R$ with $\tau \le g(T)$
satisfies $|S| \le |T|$: among the sets met during backward selection, the returned SIS has the
smallest cardinality among the sufficient ones.
