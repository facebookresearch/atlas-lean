# Restriction commutes with an allowed prefix up to weak bisimilarity in static CCS

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. An action $\mu$ is allowed by $L$ when $\mu = \tau$ or $\mu$ is an input or an output on a name not in $L$. For every finite list $L$ of names, every CCS label $\alpha$ allowed by $L$ and every process $P$, $(\alpha.P) \setminus L$ and $\alpha.(P \setminus L)$ are weakly bisimilar in this transition system: some bisimulation of the saturated system, whose transitions are the weak transitions, relates them.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3 and 5 (ISBN 978-0-13-115007-2).
