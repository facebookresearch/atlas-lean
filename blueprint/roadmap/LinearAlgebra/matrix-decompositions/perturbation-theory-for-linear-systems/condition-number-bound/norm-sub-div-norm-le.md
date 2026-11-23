# Condition number bound for linear systems

Let $A$ be an invertible bounded operator on a Banach space (for instance a nonsingular square matrix with an operator norm), with $Ax = b \ne 0$, and let $(A - E)(x + \delta x) = b + f$ with $\|E\|\,\|A^{-1}\| < 1$. Then

$$\frac{\|\delta x\|}{\|x\|} \le \frac{\|A\|\,\|A^{-1}\|}{1 - \|E\|\,\|A^{-1}\|} \left(\frac{\|f\|}{\|b\|} + \frac{\|E\|}{\|A\|}\right).$$

The relative error in $x$ is at most the condition number $\kappa(A) = \|A\|\,\|A^{-1}\|$, times a factor close to 1 unless $A$ is nearly singular, times the sum of the relative changes in $b$ and in $A$ (J. W. Demmel, Math 221 Lecture 3 notes, UC Berkeley, 2024). A backward stable algorithm makes $\|f\|/\|b\|$ and $\|E\|/\|A\|$ of the order of the machine precision $\varepsilon$, so its relative error is $O(\kappa(A)\,\varepsilon)$.

**Proof.** Subtracting $Ax = b$ gives $(A - E)\,\delta x = f + E x$, so $\delta x = (A - E)^{-1}(f + Ex)$ and $\|\delta x\| \le \|(A - E)^{-1}\|\,(\|f\| + \|E\|\,\|x\|)$. Divide by $\|x\|$ and use $\|b\| \le \|A\|\,\|x\|$.

## Informally uses

- [Norm of the inverse under perturbation](norm-inverse-sub-le.md): bounds $\|(A - E)^{-1}\|$ by $\|A^{-1}\|/(1 - \|E\|\,\|A^{-1}\|)$.
