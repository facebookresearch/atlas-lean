# Rooted weak transitions of the left component lift through parallel composition in static CCS

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A rooted weak transition from $P$ to $P'$ with label $\mu$ is a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$; it always contains the actual $\mu$-transition, also when $\mu = \tau$. If there is a rooted weak transition from $P$ to $P'$ with label $\mu$, then for every process $Q$ there is one from $P \mid Q$ to $P' \mid Q$ with label $\mu$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
