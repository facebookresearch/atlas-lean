# Knill–Laflamme conditions for the bit-flip code

Let $P$ be the [projector](code-projector.md) onto the span of $|000\rangle$ and $|111\rangle$,
and let $E$ and $E'$ be the identity or a [single bit flip](single-flip.md). Then

$$P E^{*} E' P = c P, \qquad c = \begin{cases} 1 & E = E', \\ 0 & E \ne E'. \end{cases}$$

These are the Knill–Laflamme conditions in Preskill's form (7.19), with $C$ the identity matrix:
the code is nondegenerate for this error set (equation (7.15)).

The proof uses the [product formula for Pauli operators](../distance-of-a-quantum-code/conj-transpose-pauli-mul-pauli.md):
$E^{*} E' = X^{c}$ with $c$ the sum of the two flip patterns, a vector of weight at most $2$. The
matrix $P X^{c} P$ has entry $1$ at $(u, v)$ exactly when $u, v \in \{000, 111\}$ and
$u = v + c$. If $c = 0$ this is $P$; otherwise $c = u + v$ would be $000$ or $111$, which a
nonzero vector of weight at most $2$ is not, so $P X^{c} P = 0$. This is a finite check over
the $16$ pairs of errors and $64$ pairs of basis states.

## Background

- [The code projector is an orthogonal projector](code-projector-is-proj.md): the companion fact that makes $P$ a valid code projector for the Knill–Laflamme theorem; the computation here uses only the diagonal form of $P$.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2, equations (7.15) and (7.19), applied to the code of Section 7.1.
