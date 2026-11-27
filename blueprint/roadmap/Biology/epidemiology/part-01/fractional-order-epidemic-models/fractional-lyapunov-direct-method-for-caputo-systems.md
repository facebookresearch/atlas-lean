# Fractional Lyapunov direct method for Caputo systems

**Setting.** Let $0<p<1$ and consider the Caputo system ${}^{C}D^{p}_t x(t) = f(t, x(t))$ with $f(t, 0) = 0$, so $x^* = 0$ is an equilibrium (translate a general equilibrium to the origin), where ${}^{C}D^{p}_t$ is the [Caputo derivative](caputo-fractional-derivative.md).

**Theorem.** Suppose there are a continuously differentiable function $L(t, x)$ and continuous positive definite functions $M_1, M_2, M_3$ on a neighbourhood $D$ of $0$ such that, along solutions in $D$,

$$M_1(x) \le L(t, x) \le M_2(x), \qquad {}^{C}D^{p}_t L(t, x(t)) \le -M_3(x(t)).$$

Then $x^* = 0$ is uniformly asymptotically stable.

## Depends on

- [Caputo fractional derivative](caputo-fractional-derivative.md)
- [Well-posedness of Caputo fractional initial value problems](caputo-fractional-initial-value-problem-well-posedness.md)

## Proof depends on

- [Generalized mean value theorem for Caputo derivatives](generalized-mean-value-theorem-for-caputo-derivatives.md)

## Expansion

The proof follows the integer-order argument with the fractional comparison principle in place of integration of $\dot L \le 0$: ${}^{C}D^{p}_t L \le 0$ keeps $L(t, x(t))$ below its initial value, by the [generalized mean value theorem](generalized-mean-value-theorem-for-caputo-derivatives.md), which gives uniform stability, and the bound $-M_3$ forces $L$ to decrease to $0$, which gives attractivity. In epidemic applications $L$ is a linear combination $\sum_j A_j x_j$ of infected compartments for the disease-free equilibrium, whose Caputo derivative is the same linear combination of the right-hand sides because the derivative is linear, or a Volterra-type function for an endemic equilibrium, handled by the [Volterra-type Lyapunov inequalities](volterra-lyapunov-inequalities-for-caputo-derivatives.md). With polynomial bounds $M_1 = a_1\|x\|^{a}$, $M_2 = a_2\|x\|^{ab}$, $M_3 = a_3\|x\|^{ab}$ the conclusion strengthens to Mittag-Leffler stability.

## Sources

- M. Awais, F. S. Alshammari, S. Ullah, M. A. Khan, S. Islam, "Modeling and simulation of the novel coronavirus in Caputo derivative", Results in Physics (2020), Theorem 0.1 (fractional Lyapunov direct method) and Theorem 0.4 (global stability with a linear Lyapunov function), <https://doi.org/10.1016/j.rinp.2020.103588> (PMC7671651).
- Y. Li, Y. Chen, I. Podlubny, "Stability of fractional-order nonlinear dynamic systems: Lyapunov direct method and generalized Mittag–Leffler stability", Computers & Mathematics with Applications 59 (2010) 1810–1821, <https://doi.org/10.1016/j.camwa.2009.08.019>.
