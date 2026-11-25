# Completeness of d-separation

**Completeness of d-separation** (Geiger, Verma and Pearl 1990; Pearl 1995, §2.1: the
conditional independencies implied by the factorization over a DAG are exactly the
d-separations; Meek 1995, Theorem 1 and footnote 1, for a fixed discrete state space): let $B$
be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite type $\alpha$ with
at least two elements. If pairwise disjoint finite sets $X, Y, Z$ of nodes are such that $Z$
does not d-separate $X$ from $Y$ in the graph of $B$, then some Bayesian network with the same
parent sets as $B$ and values in $\alpha$ makes $X$ and $Y$ conditionally dependent given $Z$
under its joint distribution.

Together with the global Markov property this says that d-separation cannot be improved
upon as a graphical test of conditional independence (Meek 1995 shows more: for a fixed
discrete state space almost all parameter values give a faithful distribution).

## Background

- [The global Markov property](cond-indep-of-d-separated.md): the soundness direction.
