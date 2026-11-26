# Laplace transform of the matrix exponential and of the state of a linear system

Let $A \in \mathbb{C}^{n \times n}$, and let $M \ge 1$ and $\alpha \in \mathbb{R}$ satisfy $\|e^{tA}\| \le M e^{\alpha t}$ for all $t \ge 0$. Such $M$ exist for every $\alpha$ larger than the real parts of all eigenvalues of $A$. Write $\hat F(s) = \int_0^\infty e^{-st} F(t)\, dt$ for the one-sided Laplace transform.

1. **Resolvent.** For every $s \in \mathbb{C}$ with $\operatorname{Re} s > \alpha$, the integral $\int_0^\infty e^{-st} e^{tA}\, dt$ converges absolutely. The matrix $sI - A$ is invertible, and

    $$\int_0^\infty e^{-st} e^{tA}\, dt = (sI - A)^{-1}.$$

2. **Growth of the state.** Let $B \in \mathbb{C}^{n \times m}$, $x_0 \in \mathbb{C}^n$, and let $u : [0, \infty) \to \mathbb{C}^m$ be locally integrable with $\|u(t)\| \le K e^{\beta t}$ for some $K \ge 0$ and $\beta \in \mathbb{R}$. Then the variation-of-constants state $x(t) = e^{tA} x_0 + \int_0^t e^{(t - \tau) A} B u(\tau)\, d\tau$ satisfies

    $$\|x(t)\| \le M \big(\|x_0\| + K \|B\|\, t\big) e^{\gamma t} \qquad (t \ge 0), \qquad \gamma = \max(\alpha, \beta).$$

3. **Transfer identity.** For $\operatorname{Re} s > \max(\alpha, \beta)$, the transforms $\hat x(s)$ and $\hat u(s)$ converge absolutely, and

    $$\hat x(s) = (sI - A)^{-1} \big(x_0 + B\, \hat u(s)\big).$$

    For an output $y = Cx + Du$, $\hat y(s) = C \hat x(s) + D \hat u(s)$. With $x_0 = 0$ this gives $\hat y(s) = \big(C (sI - A)^{-1} B + D\big) \hat u(s)$.

The half-plane cannot be replaced by invertibility of $sI - A$. For $n = 1$, $A = 1$ and $s = 1/2$, the number $s - A = -1/2$ is invertible, but $\int_0^\infty e^{-t/2} e^{t}\, dt$ diverges.

**Proof.**

- **Part 1.** $\frac{d}{dt} e^{t(A - sI)} = (A - sI) e^{t(A - sI)}$ and $\|e^{t(A - sI)}\| \le M e^{(\alpha - \operatorname{Re} s) t} \to 0$. Integrating over $[0, T]$ and letting $T \to \infty$ gives $(A - sI) \int_0^\infty e^{t(A - sI)}\, dt = -I$.
- **Part 2.** Bound the integrand by $M e^{\alpha (t - \tau)} \|B\| K e^{\beta \tau} \le M \|B\| K e^{\gamma t}$.
- **Part 3.** The double integral $\int_0^\infty \int_0^t e^{-st} e^{(t - \tau) A} B u(\tau)\, d\tau\, dt$ is absolutely convergent by the bounds $M e^{(\alpha - \operatorname{Re} s)(t - \tau)}$ and $K \|B\| e^{(\beta - \operatorname{Re} s)\tau}$. Substituting $t = \tau + r$ on the triangle $0 \le \tau \le t$ factors it as $\big(\int_0^\infty e^{-sr} e^{rA}\, dr\big) B \hat u(s)$, and part 1 identifies the first factor.

## Depends on

- [The one-sided Laplace transform](../../harmonic-analysis/integral-transforms/laplace-transform/laplace.md): the one-sided Laplace transform
- [Convergence of the Laplace transform under an exponential bound](../../harmonic-analysis/integral-transforms/laplace-transform/laplace-convergent-of-norm-le-exp.md): absolute convergence under an exponential bound

## Background

- [Duhamel's formula (variation of constants)](../../ordinary-differential-equations/duhamel-variation-of-constants.md): for continuous $u$ the variation-of-constants state solves $\dot x = Ax + Bu$, $x(0) = x_0$
- [Controller-form realization of a proper rational transfer matrix](controller-form-realization-of-a-proper-rational-transfer-matrix.md): the transfer matrix $C(sI - A)^{-1}B + D$ as a rational matrix

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 7.4: the Laplace transform of a matrix function of exponential growth and its analyticity for $\operatorname{Re} s > \sigma$ (p. 332), the transfer matrix $W = \hat K$ with $\hat\eta = W \hat\omega$ (pp. 332–333), and the transform $s\hat\xi(s) - \xi(0)$ of $\dot\xi$ by integration by parts, with $\hat\eta = C (sI - A)^{-1} B \hat\omega$ when $\xi(0) = 0$ (p. 334). The resolvent identity of part 1 and the identity of part 3 for nonzero $x_0$ are derived above.
