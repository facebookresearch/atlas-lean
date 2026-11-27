# Silent steps of the right component lift through parallel composition in CCS with communication

Let the channel names form a type with decidable equality, and consider the finite CCS processes whose actions are CCS labels (the silent label $\tau$, inputs and outputs on names) with the transition relation of CCS with communication, in which an input and an output on the same name performed by the two components of a parallel composition synchronize to $\tau$. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. If $Q \Rightarrow Q'$, then $P \mid Q \Rightarrow P \mid Q'$ for every process $P$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
