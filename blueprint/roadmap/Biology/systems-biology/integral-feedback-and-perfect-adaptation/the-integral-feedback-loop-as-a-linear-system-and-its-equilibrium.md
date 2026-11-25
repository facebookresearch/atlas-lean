# The integral-feedback loop as a linear system and its equilibrium

Let $a, b > 0$ and consider the loop in which an output $e$ is driven by a constant input $r$ and corrected through the integral $z$ of $e$:

$$\dot e = -a e - b z + r, \qquad \dot z = e.$$

1. **State-space form.** With state $\xi = (e, z)$ this is the linear system $\dot\xi = A\xi + Br$, $y = C\xi + Dr$, with

    $$A = \begin{bmatrix} -a & -b \\ 1 & 0 \end{bmatrix}, \quad B = \begin{bmatrix} 1 \\ 0 \end{bmatrix}, \quad C = \begin{bmatrix} 1 & 0 \end{bmatrix}, \quad D = 0 .$$

2. **Unique equilibrium.** For each constant $r$, the system has exactly one equilibrium, $(e, z) = (0, r/b)$; at it the output $e$ is $0$ whatever the value of $r$.
3. **Zero DC gain.** The steady-state gain from $r$ to $e$ is $D - CA^{-1}B = 0$.

The integrator state $z$ settles to whatever value cancels the input, which is the mechanism behind perfect adaptation.

**Proof.** Part 1 is a direct rewriting. For part 2, $\dot z = 0$ forces $e = 0$, and then $\dot e = 0$ gives $z = r/b$; equivalently $A$ is invertible since $\det A = b \ne 0$, so $A\xi + Br = 0$ has the unique solution $\xi = -A^{-1}Br = (0, r/b)$. Part 3 follows: $CA^{-1}B$ is the first coordinate of $A^{-1}B = (0, -1/b)$, which is $0$.

## Background

- [Integral feedback implies perfect adaptation](has-perfect-adaptation-of-has-integral-f.md): the general statement for linear systems with integral feedback
- [Unique equilibrium of a nonsingular linear system](field-eq-zero-iff.md): the equilibrium $-A^{-1}Br$
- [Steady-state (DC) gain of a linear system](dc-gain.md): the gain $D - CA^{-1}B$

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021, <https://fbswiki.org/>, Section 7.4, integral action: the augmented state $\dot z = y - r$ (7.26), and the observation that at any stable equilibrium $\dot z = 0$ forces the output to its reference, with the integrator state settling to the value that cancels the input (pp. 7-25–7-26). The explicit matrices and equilibrium are computed on the page.
