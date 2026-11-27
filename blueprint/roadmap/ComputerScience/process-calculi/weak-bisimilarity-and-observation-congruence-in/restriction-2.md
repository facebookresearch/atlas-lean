# Allowed weak transitions lift through restriction

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A weak transition $P \stackrel{\mu}{\Longrightarrow} P'$ is either the trivial one $P \stackrel{\tau}{\Longrightarrow} P$ or a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$. An action $\mu$ is allowed by $L$ when $\mu = \tau$ or $\mu$ is an input or an output on a name not in $L$. If $P \stackrel{\mu}{\Longrightarrow} P'$ and $\mu$ is allowed by $L$, then $P \setminus L \stackrel{\mu}{\Longrightarrow} P' \setminus L$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
