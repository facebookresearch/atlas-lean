# Forward simulations are sound for trace inclusion

A *forward simulation* from an automaton $A$ to an automaton $B$ is a relation $f$ between the states of $A$ and those of $B$ such that

1. for every start state $s$ of $A$, the set $f[s]$ of states related to $s$ contains a start state of $B$, and
2. if $s' \xrightarrow{a}_A s$ and $u' \in f[s']$, then there is $u \in f[s]$ with $u' \overset{\hat a}{\Longrightarrow}_B u$.

Write $A \le_F B$ if there is a forward simulation from $A$ to $B$. If $A \le_F B$, then $A \le_T B$: every finite or infinite trace of $A$ is a trace of $B$. The relation $\le_F$ is a preorder. Every *refinement*, a function $r$ that maps start states to start states and satisfies $r(s') \overset{\hat a}{\Longrightarrow}_B r(s)$ whenever $s' \xrightarrow{a}_A s$, is a forward simulation.

## Depends on

- [Automata and trace inclusion](automata-and-trace-inclusion.md)

## Sources

- N. Lynch and F. Vaandrager, "Forward and backward simulations, Part I: Untimed systems", *Information and Computation* 121(2):214–233, 1995; author version of the journal paper, October 31, 1994, <https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf>, Section 3.1 (refinements), Section 3.2, the definition of forward simulations, Propositions 3.7 and 3.9 and Theorem 3.10.
