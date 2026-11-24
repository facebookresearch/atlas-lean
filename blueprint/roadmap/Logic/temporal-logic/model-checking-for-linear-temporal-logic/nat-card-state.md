# Exact state count of the LTL tableau

The truth-annotation tableau of an LTL formula $\varphi$ has exactly $2^{|\varphi|}$ states: a
state assigns one truth value to each syntactic occurrence in $\varphi$.

This is the exponential state space of the Vardi–Wolper construction, where a state is a set
of subformulas. The count here is over occurrences rather than distinct subformulas, so it is
exact for this tableau and an upper bound for the subformula-set construction up to sharing of
repeated subformulas.

## Background

- [Truth-annotation states of the LTL tableau](state.md): the state type being counted.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 3, Corollary 23.
