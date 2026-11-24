# Parallel composition is commutative up to weak bisimilarity

Let the channel names form a type with decidable equality, and consider the finite CCS processes whose actions are CCS labels (the silent label $\tau$, inputs and outputs on names) with the transition relation of CCS with communication, in which an input and an output on the same name performed by the two components of a parallel composition synchronize to $\tau$. For all processes $P$ and $Q$, $P \mid Q$ and $Q \mid P$ are weakly bisimilar: some bisimulation of the saturated system, whose transitions are the weak transitions, relates them.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
