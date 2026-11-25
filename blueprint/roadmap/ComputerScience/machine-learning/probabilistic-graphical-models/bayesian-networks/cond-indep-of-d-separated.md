# The global Markov property

**The global Markov property** (soundness of d-separation: Geiger, Verma & Pearl 1990;
Lauritzen, Dawid, Larsen & Leimer 1990): let $B$ be a Bayesian network on the nodes
$0, \dots, n - 1$ with values in a finite nonempty type $\alpha$. If $Z$ d-separates $X$ from
$Y$ in the graph of $B$, then $X$ and $Y$ are conditionally independent given $Z$ under the
joint distribution of $B$. No disjointness of $X$, $Y$, $Z$ is needed.

## Background

- [Completeness of d-separation](exists-not-cond-indep-of-not-d-separated.md): the converse.
