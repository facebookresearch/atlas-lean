# Change of the inverse

In a complete normed ring, if $A$ is invertible with $Z = A^{-1}$ and $\|E\|\,\|Z\| < 1$, then

$$\|(A - E)^{-1} - Z\| \le \frac{\|Z\|^2\,\|E\|}{1 - \|E\|\,\|Z\|}.$$

Dividing by $\|Z\|$, the relative change of the inverse is at most $\kappa(A)/(1 - \|E\|\,\|Z\|)$ times the relative change $\|E\|/\|A\|$ of $A$, with $\kappa(A) = \|A\|\,\|Z\|$; this is how Demmel's Math 221 Lecture 3 notes (UC Berkeley, 2024) motivate the definition of the condition number.

## Informally uses

- [Norm of the inverse under perturbation](norm-inverse-sub-le.md): $(A - E)^{-1} - Z = Z E (A - E)^{-1}$, and the norm of $(A - E)^{-1}$ is bounded there.
