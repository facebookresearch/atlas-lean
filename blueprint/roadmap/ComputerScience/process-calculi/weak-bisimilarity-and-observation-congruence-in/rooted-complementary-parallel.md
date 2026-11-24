# Complementary rooted weak transitions synchronize to a rooted silent transition in static CCS

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A rooted weak transition from $P$ to $P'$ with label $\mu$ is a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$; it always contains the actual $\mu$-transition, also when $\mu = \tau$. Two labels are complementary when one is the input and the other the output on the same name; $\tau$ is complementary to no label. If there are rooted weak transitions from $P$ to $P'$ with label $\alpha$ and from $Q$ to $Q'$ with label $\beta$, where $\alpha$ and $\beta$ are complementary, then there is a rooted weak transition from $P \mid Q$ to $P' \mid Q'$ with label $\tau$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
