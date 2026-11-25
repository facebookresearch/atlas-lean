# Laplace transform of a derivative

Let $E$ be a complex Banach space and $x : \mathbb{R} \to E$. Suppose $x$ is differentiable on $[0, \infty)$, with a right derivative at $0$, its derivative $x'$ is continuous on $[0, \infty)$, and there are $M \ge 0$ and $a \in \mathbb{R}$ with $\|x(t)\| \le M e^{at}$ and $\|x'(t)\| \le M e^{at}$ for every $t \ge 0$. Write $\mathcal{L}g(s) = \int_{(0, \infty)} e^{-st} g(t)\, dt$ for the one-sided Laplace transform. Then for every $s \in \mathbb{C}$ with $\operatorname{Re} s > a$, the Laplace transforms of $x$ and $x'$ converge at $s$ and

$$\mathcal{L}x'(s) = s\, \mathcal{L}x(s) - x(0).$$

The hypotheses are those of a continuously differentiable signal; a merely locally absolutely continuous $x$ with an almost-everywhere derivative needs a separate statement.

**Proof.** Both transforms converge at $s$ by the exponential bounds. For $T > 0$, the product rule for $t \mapsto e^{-st} x(t)$ and the fundamental theorem of calculus on $[0, T]$ give

$$\int_0^T e^{-st} x'(t)\, dt = e^{-sT} x(T) - x(0) + s \int_0^T e^{-st} x(t)\, dt .$$

As $T \to \infty$, $\|e^{-sT} x(T)\| \le M e^{(a - \operatorname{Re} s) T} \to 0$, and the two integrals converge to the Laplace transforms by dominated convergence.

## Proof depends on

- [Convergence of the Laplace transform under an exponential bound](laplace-convergent-of-norm-le-exp.md): convergence of $\mathcal{L}x$ and $\mathcal{L}x'$ for $\operatorname{Re} s > a$

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 7.4 (p. 334): for a solution $\xi$ of $\dot\xi = A\xi + B\omega$ with an input of exponential growth, $\xi$ and $\dot\xi$ have exponential growth and an integration by parts shows that the transform of $\dot\xi$ is $s\hat\xi(s) - \xi(0)$. The Banach-valued statement with explicit growth hypotheses on $x$ and $x'$ and the proof are on the page.
