# Norm of the inverse under perturbation

In a complete normed ring, if $A$ is invertible with $Z = A^{-1}$ and $\|E\|\,\|Z\| < 1$, then

$$\|(A - E)^{-1}\| \le \frac{\|Z\|}{1 - \|E\|\,\|Z\|}$$

(J. W. Demmel, Math 221 Lecture 3 notes, UC Berkeley, 2024). The notes take norms in the Neumann series; the proof here uses the identity $(A - E)^{-1} = Z + Z E (A - E)^{-1}$ instead, which gives $\|(A-E)^{-1}\| \le \|Z\| + \|Z\|\,\|E\|\,\|(A-E)^{-1}\|$.

## Informally uses

- [Small perturbations of an invertible element stay invertible](is-unit-sub.md): $A - E$ is invertible, so its inverse is defined.
