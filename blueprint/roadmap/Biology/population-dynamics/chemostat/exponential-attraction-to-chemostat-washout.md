# Exponential attraction to chemostat washout above the critical dilution rate

For the chemostat with dilution rate $D > 0$, feed substrate concentration $S_f > 0$, yield $y > 0$ and Monod growth rate
$\mu(S) = \mu_m S / (K_s + S)$, $\mu_m, K_s > 0$, the chemostat balances for biomass $X$ and substrate
$S$ are

$$\frac{dX}{dt} = \bigl(\mu(S) - D\bigr) X, \qquad
\frac{dS}{dt} = D (S_f - S) - \frac{1}{y} \, \mu(S) X .$$

The Jacobian matrix of the right-hand side at the [washout steady state](chemostat-equilibria-and-washout.md)
$(X, S) = (0, S_f)$ is

$$J = \begin{pmatrix} \mu(S_f) - D & 0 \\ -\mu(S_f)/y & -D \end{pmatrix},$$

with eigenvalues $\mu(S_f) - D$ and $-D$. If $D > D_c = \mu(S_f)$, then
$\operatorname{tr} J < 0$ and $\det J = -D(\mu(S_f) - D) > 0$, so $J$ is Hurwitz. Consequently, with
the maximum norm on $(X, S)$, there are $\delta, C, \alpha > 0$ such that every solution defined for
all $t \ge 0$ whose initial value lies within distance $\delta$ of $(0, S_f)$ satisfies

$$\|(X(t), S(t)) - (0, S_f)\| \le C e^{-\alpha t} \|(X(0), S(0)) - (0, S_f)\| \qquad (t \ge 0).$$

Like the principle it rests on, this statement is conditional on the solution existing on
$[0, \infty)$; it is not by itself an existence result. At $D = D_c$ one eigenvalue is $0$ and the
criterion does not apply.

The lower-left entry is $\partial_X$ of the substrate equation, $-\mu(S_f)/y$; the Jacobian printed in
the source exercise below has the opposite sign there, while differentiating Equation 10.18 gives the
entry above. The conclusion follows from the
[linearized stability principle](../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md) applied to the right-hand side, which is smooth near
$(0, S_f)$ because $K_s + S > 0$ there.

## Depends on

## Proof depends on

- [Chemostat equilibria and the washout threshold](chemostat-equilibria-and-washout.md), for washout as a steady state
- [Linearized stability principle](../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md), for exponential decay at an equilibrium with Hurwitz linearization

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 10.5, Equation 10.18 (p. 596) and the statement that the washout steady state is
  stable for $D > D_c$ and unstable for $D < D_c$ (p. 597); Exercise 10.7 (p. 615), which asks for the
  Jacobian of Equations 10.18.
