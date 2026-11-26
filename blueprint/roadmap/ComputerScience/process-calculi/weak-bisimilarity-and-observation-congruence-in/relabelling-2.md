# Weak transitions lift through relabelling

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A weak transition $P \stackrel{\mu}{\Longrightarrow} P'$ is either the trivial one $P \stackrel{\tau}{\Longrightarrow} P$ or a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$. For a relabelling $f$, write $f(\mu)$ for the relabelled action: $f(\tau) = \tau$, the input on $a$ goes to the visible label $f(a)$ that $f$ assigns to $a$, and the output on $a$ goes to the complement of $f(a)$. If $P \stackrel{\mu}{\Longrightarrow} P'$, then $P[f] \stackrel{f(\mu)}{\Longrightarrow} P'[f]$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
