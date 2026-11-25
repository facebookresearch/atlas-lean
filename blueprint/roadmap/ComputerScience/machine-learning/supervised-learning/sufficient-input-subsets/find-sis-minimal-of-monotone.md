# Minimality of FindSIS for monotone set functions

Let $g$ be a real function on the finite subsets of a set of features that is monotone for
inclusion (masking more features never raises the prediction), $\tau \in \mathbb{R}$ and $\pi$ a
[greedy backward-selection rule](is-greedy.md) for $g$. If [FindSIS](find-sis.md) returns $S$,
then $S$ is inclusion-minimal: every proper subset $T \subsetneq S$ has $g(T) < \tau$. (Derived;
the paper states only Proposition 1.)
