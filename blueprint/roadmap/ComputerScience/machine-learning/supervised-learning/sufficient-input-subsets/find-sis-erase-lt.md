# No feature of the FindSIS output can be masked

**Proposition 1 (first part)** of Carter et al.: let $g$ be a real function on the finite
subsets of a set of features, $\tau \in \mathbb{R}$ a threshold and $\pi$ a
[greedy backward-selection rule](is-greedy.md) for $g$. If [FindSIS](find-sis.md) returns $S$
from a finite set $R$, then no feature of $S$ can be additionally masked while keeping the
prediction at or above the threshold: $g(S \setminus \{s\}) < \tau$ for every $s \in S$.
