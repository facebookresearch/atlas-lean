# Rooted weak transitions lift through relabelling

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A rooted weak transition from $P$ to $P'$ with label $\mu$ is a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$; it always contains the actual $\mu$-transition, also when $\mu = \tau$. For a relabelling $f$, write $f(\mu)$ for the relabelled action: $f(\tau) = \tau$, the input on $a$ goes to the visible label $f(a)$ that $f$ assigns to $a$, and the output on $a$ goes to the complement of $f(a)$. If there is a rooted weak transition from $P$ to $P'$ with label $\mu$, then there is one from $P[f]$ to $P'[f]$ with label $f(\mu)$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
