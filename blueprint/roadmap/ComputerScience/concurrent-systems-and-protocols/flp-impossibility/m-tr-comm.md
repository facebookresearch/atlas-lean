# Commutativity of disjoint schedules

Let $a$ be an algorithm, $s$ a state and $ps$ a set of processes. Suppose the finite schedule $xs_1$ leads from $s$ to $s_1$ and the finite schedule $xs_2$ leads from $s$ to $s_2$, where every message received in $xs_1$ is addressed to a process of $ps$ and every message received in $xs_2$ to a process outside $ps$. Then $xs_2$ leads from $s_1$ and $xs_1$ leads from $s_2$ to one and the same state. This is Lemma 1 of Fischer, Lynch and Paterson (1985), in the model of these pages: schedules run by disjoint sets of processes do not interact.

It is stronger than the diamond property of reachability restricted to two disjoint sets of processes, which only gives a common state reached by some schedules of the two sets; here the given schedules themselves commute, as in the source.

## Sources

- M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one faulty process*, Journal of the ACM 32(2), 1985, 374–382: Lemma 1.
