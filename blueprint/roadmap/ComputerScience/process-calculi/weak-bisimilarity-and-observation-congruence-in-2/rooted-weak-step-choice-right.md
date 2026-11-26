# A rooted weak transition of the right summand is one of the choice

Let $A$ be a type of actions with a distinguished silent action $\tau$, and consider the finite CCS processes over $A$ (built from $\mathbf{0}$ by prefix $a.P$, choice $P + Q$ and parallel composition $P \mid Q$) with the transitions of finite CCS without communication. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A rooted weak transition from $P$ to $P'$ with label $\mu$ is a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$; it always contains the actual $\mu$-transition, also when $\mu = \tau$. If there is a rooted weak transition from $Q$ to $Q'$ with label $\mu$, then for every process $P$ there is a rooted weak transition from $P + Q$ to $Q'$ with label $\mu$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
