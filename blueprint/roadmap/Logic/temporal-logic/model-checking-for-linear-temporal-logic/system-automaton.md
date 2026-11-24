# Büchi automaton of a transition system

The Büchi automaton $A_P$ of a transition system with initial states $I$ has the states of
the system as states and as letters, $I$ as initial states, and a transition from $s$ to $t$
reading $s$ whenever the system has a transition from $s$ to $t$; every state is accepting, so
every infinite run is accepting.

Vardi's $A_P$ reads the label $V(s) \subseteq Prop$ of the current state instead of the state
itself; that is the special case of a valuation on states given by $V$.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 4.2.
