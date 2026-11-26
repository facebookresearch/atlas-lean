# Backward simulations are sound for trace inclusion

A *backward simulation* from an automaton $A$ to an automaton $B$ is a total relation $b$ between the states of $A$ and those of $B$, so that every state $s$ of $A$ has a nonempty image $b[s]$, such that

1. for every start state $s$ of $A$, $b[s]$ consists of start states of $B$, and
2. if $s' \xrightarrow{a}_A s$ and $u \in b[s]$, then there is $u' \in b[s']$ with $u' \overset{\hat a}{\Longrightarrow}_B u$.

Write $A \le_B B$ if there is a backward simulation from $A$ to $B$, and $A \le_{iB} B$ if there is one that is image-finite. Then

1. $A \le_B B$ implies $A \le_{\ast T} B$, and
2. $A \le_{iB} B$ implies $A \le_T B$.

Image-finiteness is needed for infinite traces: the futures of a state can be infinite, while its histories are finite executions.

## Depends on

- [Automata and trace inclusion](automata-and-trace-inclusion.md)

## Sources

- N. Lynch and F. Vaandrager, "Forward and backward simulations, Part I: Untimed systems", *Information and Computation* 121(2):214–233, 1995; author version of the journal paper, October 31, 1994, <https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf>, Section 3.3, the definition of backward simulations, Lemma 3.15 and Theorem 3.17.
