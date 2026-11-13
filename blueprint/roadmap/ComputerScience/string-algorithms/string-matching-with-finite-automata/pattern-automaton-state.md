# The string-matching automaton tracks the longest matched prefix

Let $P$ be a pattern of
length $m$ over the alphabet $\{0, \dots, A-1\}$ and write $P_k$ for its prefix of length $k$.
For every word $w$ over this alphabet, the state that the string-matching automaton of $P$
reaches from its start state after reading $w$ is the greatest $k \le m$ such that $P_k$ is a
suffix of $w$.
