# Exact cost of the finite-automaton matcher

For every pattern $P$ and text $T$ over the
alphabet $\{0, \dots, A-1\}$, where $T$ has length $n$, the cost of the finite-automaton matcher
on $P$ and $T$ equals the cost of computing the transition table of $P$, plus $2n$, plus the
number of shifts the matcher returns.
