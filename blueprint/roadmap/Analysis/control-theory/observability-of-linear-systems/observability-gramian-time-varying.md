# Observability Gramian of a time-varying linear system

Let $A : \mathbb{R} \to \mathbb{R}^{n \times n}$ and $C : \mathbb{R} \to \mathbb{R}^{p \times n}$ be continuous, let $\Phi(t, s)$ be the [transition matrix](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md) of $\dot x = A(t) x$, and fix $t_0 < t_1$. The **zero-input output map** on $[t_0, t_1]$ sends an initial state $x \in \mathbb{R}^n$ to the output $t \mapsto C(t) \Phi(t, t_0) x$ of $\dot x = A(t) x$, $y = C(t) x$, $x(t_0) = x$, on $[t_0, t_1]$. Let

$$W_o(t_0, t_1) = \int_{t_0}^{t_1} \Phi(s, t_0)^\top C(s)^\top C(s)\, \Phi(s, t_0) \, ds .$$

Then the zero-input output map is injective if and only if $W_o(t_0, t_1)$ is positive definite, equivalently has rank $n$. In that case the initial state is recovered from the zero-input output $\eta(t) = C(t) \Phi(t, t_0) x$ by

$$x = W_o(t_0, t_1)^{-1} \int_{t_0}^{t_1} \Phi(s, t_0)^\top C(s)^\top \eta(s) \, ds .$$

For a system with inputs, $\dot x = A(t) x + B(t) u$ with $B$ and the inputs continuous, two initial states give the same output under the same input exactly when their difference has zero zero-input output, because the input contributes the same term to both outputs; so the criterion characterizes observability on $[t_0, t_1]$.

Proof: $W_o$ is symmetric and $x^\top W_o x = \int_{t_0}^{t_1} \|C(s) \Phi(s, t_0) x\|^2 \, ds \ge 0$, so $W_o$ is positive semidefinite, and it is positive definite exactly when it has rank $n$. Since the integrand is continuous, $x^\top W_o x = 0$ if and only if $C(s) \Phi(s, t_0) x = 0$ for every $s \in [t_0, t_1]$, that is, $x$ lies in the kernel of the zero-input output map. The reconstruction formula is $W_o x = \int \Phi^\top C^\top \eta$.

## Depends on

- [Variation of constants for time-varying linear systems](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md): the transition matrix $\Phi$.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 6.3: Exercise 6.3.2 (p. 279), stated there for measurable locally essentially bounded coefficients; observability on an interval is Definition 6.1.4, and its reduction to the zero input for linear systems is Corollary 6.1.6 (pp. 263–264).
