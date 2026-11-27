# Exponential state bound for the Büchi automaton of an LTL formula

The nondeterministic Büchi automaton of an LTL formula $\varphi$, obtained by degeneralizing its
tableau, has at most $4^{|\varphi|} = 2^{2|\varphi|}$ states.

Its states are pairs of a truth annotation and a fairness counter with at most $|\varphi|$
values, so there are at most $|\varphi| \cdot 2^{|\varphi|} \le 4^{|\varphi|}$ of them.

## Informally uses

- [Exact state count of the LTL tableau](nat-card-state.md): the $2^{|\varphi|}$ annotations.
- [Fairness obligations are fewer than the formula size](obligation-count-lt-size.md): the
  counter takes at most $|\varphi|$ values.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 3, Corollary 23.
