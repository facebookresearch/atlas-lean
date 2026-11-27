# Relabelling preserves weak bisimilarity

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A weak transition $P \stackrel{\mu}{\Longrightarrow} P'$ is either the trivial one $P \stackrel{\tau}{\Longrightarrow} P$ or a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$. Two processes are weakly bisimilar, $P \approx Q$, when some bisimulation of the saturated system (same states, the weak transitions as transitions) relates them. For every relabelling $f$ and all processes $P$, $Q$: if $P \approx Q$, then $P[f] \approx Q[f]$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
