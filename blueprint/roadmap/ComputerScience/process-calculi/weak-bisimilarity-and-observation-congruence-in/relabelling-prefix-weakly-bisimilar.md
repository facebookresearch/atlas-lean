# Relabelling commutes with prefix up to weak bisimilarity in static CCS

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. For a relabelling $f$, write $f(\mu)$ for the relabelled action: $f(\tau) = \tau$, the input on $a$ goes to the visible label $f(a)$ that $f$ assigns to $a$, and the output on $a$ goes to the complement of $f(a)$. For every relabelling $f$, every CCS label $\alpha$ and every process $P$, $(\alpha.P)[f]$ and $f(\alpha).(P[f])$ are weakly bisimilar in this transition system: some bisimulation of the saturated system, whose transitions are the weak transitions, relates them.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3 and 5 (ISBN 978-0-13-115007-2).
