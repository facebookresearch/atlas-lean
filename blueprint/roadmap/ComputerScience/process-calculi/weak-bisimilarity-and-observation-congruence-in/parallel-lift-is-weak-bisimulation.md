# The parallel lift of weak bisimulations is a weak bisimulation in static CCS

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A weak transition $P \stackrel{\mu}{\Longrightarrow} P'$ is either the trivial one $P \stackrel{\tau}{\Longrightarrow} P$ or a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$. A relation is a weak bisimulation when it is a bisimulation of the saturated system: each weak transition of either related process is matched by a weak transition with the same label of the other, the targets again related. The parallel lift of relations $R$ and $S$ relates $U$ to $V$ exactly when $R$ relates them, or $S$ relates them, or $U = P_1 \mid Q_1$ and $V = P_2 \mid Q_2$ with $R$ relating $P_1$ to $P_2$ and $S$ relating $Q_1$ to $Q_2$. If $R$ and $S$ are weak bisimulations, then so is their parallel lift.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
