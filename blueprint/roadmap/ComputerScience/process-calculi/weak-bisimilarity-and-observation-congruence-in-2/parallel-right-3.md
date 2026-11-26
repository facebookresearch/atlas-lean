# Rooted weak transitions of the right component lift through parallel composition in CCS with communication

Let the channel names form a type with decidable equality, and consider the finite CCS processes whose actions are CCS labels (the silent label $\tau$, inputs and outputs on names) with the transition relation of CCS with communication, in which an input and an output on the same name performed by the two components of a parallel composition synchronize to $\tau$. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A rooted weak transition from $P$ to $P'$ with label $\mu$ is a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$; it always contains the actual $\mu$-transition, also when $\mu = \tau$. If there is a rooted weak transition from $Q$ to $Q'$ with label $\mu$, then for every process $P$ there is one from $P \mid Q$ to $P \mid Q'$ with label $\mu$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
