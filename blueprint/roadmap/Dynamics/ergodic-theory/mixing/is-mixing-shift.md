# Bernoulli shifts are mixing

Let $(S, p)$ be a probability space. The Bernoulli scheme with distribution $p$ is the
[left shift](shift.md) $\sigma(x_0, x_1, x_2, \dots) = (x_1, x_2, \dots)$ on $S^{\mathbb{N}}$ with the product
measure $p^{\mathbb{N}}$. It is [mixing](is-mixing.md), whence ergodic.

This is the dynamical form of a sequence of independent identically distributed trials. A cylinder event $A$
constrains finitely many coordinates, all smaller than $n$ once $n$ is large, while $\sigma^{-n} B$ only depends
on the coordinates $\ge n$; since coordinates are independent under the product measure,
[$\mu(A \cap \sigma^{-n} B) = \mu(A)\,\mu(B)$ exactly](measure-cylinder-inter-preimage-iterate.md). A general
measurable set is approximated in measure by cylinders, which form a ring of sets generating the product
σ-algebra, and the two errors are each at most the measure of the symmetric difference.

The source states the result for a finite alphabet $S$; the proof needs no finiteness.

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), §1.5.3 (Bernoulli schemes) and Proposition 1.7.
