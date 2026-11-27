# Constant occurrences of a process

The constant occurrences of a recursive CCS
process $P$ are the list of the process constants occurring in $P$, from left to right and
with repetitions: the inactive process $\mathbf{0}$ has none; a constant $A$ has the single
occurrence $A$; a prefix $\alpha.Q$, a restriction $Q \setminus L$ and a relabelling $Q[f]$
have the occurrences of $Q$; and a choice $Q + R$ or a parallel composition $Q \mid R$ has
the occurrences of $Q$ followed by those of $R$.
