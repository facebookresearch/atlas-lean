# Weak clamping decreases the cost at the nudged equilibrium

**Setting.** As in the equilibrium propagation framework, let $F(\theta, v, \beta, s) = E(\theta, v, s) + \beta\, C(\theta, v, s)$ with $E, C$ twice continuously differentiable, and let $s^\beta = s^\beta_{\theta,v}$ be a differentiable family of fixed points satisfying $\partial_s F(\theta, v, \beta, s^\beta) = 0$ with $\partial^2_s F(\theta, v, \beta, s^\beta)$ symmetric positive definite for $\beta$ near $0$.

**Proposition.** The function $\beta \mapsto C(\theta, v, s^\beta)$ has non-positive derivative at $\beta = 0$:

$$\frac{d}{d\beta}\, C\big(\theta, v, s^{\beta}\big)\Big|_{\beta = 0} = -\left(\frac{\partial s^\beta}{\partial \beta}\Big|_{\beta=0}\right)^{\!\top} \frac{\partial^2 E}{\partial s^2}\big(\theta, v, s^0\big)\, \frac{\partial s^\beta}{\partial \beta}\Big|_{\beta=0} \le 0 .$$

Hence, unless the free equilibrium is already stationary for the cost along this direction, a small positive nudge $\beta > 0$ moves the equilibrium to a state with strictly lower cost than the free fixed point.

## Depends on

- [Equilibrium propagation gradient formula](equilibrium-propagation-gradient-formula.md)

## Expansion

Differentiating $\partial_s E(s^\beta) + \beta\, \partial_s C(s^\beta) = 0$ in $\beta$ at $\beta = 0$ gives $\partial^2_s E(s^0)\, \dot s + \partial_s C(s^0) = 0$, where $\dot s = \partial_\beta s^\beta|_{\beta=0}$. Then $\frac{d}{d\beta} C(s^\beta)|_0 = \partial_s C(s^0)^\top \dot s = -\dot s^\top \partial^2_s E(s^0)\, \dot s$, which is non-positive because the Hessian at the free fixed point is positive definite. This is why the update of the gradient formula reads as a contrastive rule: it lowers the energy of the slightly better nudged state and raises the energy of the free state.

## Sources

- B. Scellier, Y. Bengio, "Equilibrium Propagation: Bridging the Gap between Energy-Based Models and Backpropagation", Frontiers in Computational Neuroscience 11:24 (2017), Section 3.3 (Proposition 2, Eq. 25) and Appendix A (proof), <https://doi.org/10.3389/fncom.2017.00024> (PMC5415673).
