# FindSIS returns a sufficient subset of the features

Criterion (1): let $g$ be a real function on the finite subsets of a set of features,
$\tau \in \mathbb{R}$ and $\pi$ a rule choosing an element of every nonempty finite set. If
[FindSIS](find-sis.md) returns $S$ from a finite set $R$, then $S \subseteq R$ and
$\tau \le g(S)$: $S$ is a sufficient subset of the starting features.
