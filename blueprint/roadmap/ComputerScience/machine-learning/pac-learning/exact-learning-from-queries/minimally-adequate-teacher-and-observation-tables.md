# Minimally adequate teacher and observation tables

A minimally adequate teacher for an unknown regular language $U$ over a finite alphabet $\Sigma$ answers
membership queries (is $w \in U$?) and equivalence queries on a conjectured DFA $M$ (answering yes if $M$
accepts $U$, and otherwise returning a counterexample in the symmetric difference). An observation table
$(S, E, T)$ has a finite prefix-closed $S \subseteq \Sigma^*$, a finite suffix-closed $E \subseteq \Sigma^*$ and
$T : (S \cup S\Sigma)E \to \{0,1\}$ recording membership. Writing $\mathrm{row}(s)$ for $e \mapsto T(se)$, the table
is closed if every $\mathrm{row}(sa)$ equals some $\mathrm{row}(s')$ with $s' \in S$, and consistent if
$\mathrm{row}(s_1) = \mathrm{row}(s_2)$ implies $\mathrm{row}(s_1 a) = \mathrm{row}(s_2 a)$ for all $a$. A closed and
consistent table determines the conjectured DFA whose states are the rows of $S$, with initial state
$\mathrm{row}(\varepsilon)$, transitions $\mathrm{row}(s) \xrightarrow{a} \mathrm{row}(sa)$ and accepting states the rows
with $T(s) = 1$.

## Expansion

This node states a precise definition.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Finite automata (DFA, NFA, epsilon-NFA).

## Sources

- D. Angluin, *Learning regular sets from queries and counterexamples*, Information and Computation 75 (1987) 87–106: minimally adequate teachers, observation tables, closed and consistent tables and the acceptor $M(S, E, T)$ (Sections 1–2). <https://people.eecs.berkeley.edu/~dawnsong/teaching/s10/papers/angluin87.pdf>
