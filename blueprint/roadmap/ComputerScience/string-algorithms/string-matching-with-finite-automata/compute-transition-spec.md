# Correctness of the string-matching transition table

Let $P$ be a pattern of length $m$
over the alphabet $\{0, \dots, A-1\}$ and write $P_k$ for its prefix of length $k$. For every
state $q \le m$ and symbol $a < A$, the entry at index $qA + a$ of the transition table of $P$
is the greatest $k \le m$ such that $P_k$ is a suffix of the word $P_q a$.
