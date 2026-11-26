# Weak transitions of the left component lift through parallel composition in static CCS

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A weak transition $P \stackrel{\mu}{\Longrightarrow} P'$ is either the trivial one $P \stackrel{\tau}{\Longrightarrow} P$ or a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$. If $P \stackrel{\mu}{\Longrightarrow} P'$, then $P \mid Q \stackrel{\mu}{\Longrightarrow} P' \mid Q$ for every process $Q$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
