# Equilibrium propagation gradient formula

**Setting.** Let $\theta \in \mathbb{R}^p$ be parameters, $v$ a data point (input $x$ and target $d$), and $s \in \mathbb{R}^n$ the free state variables of a network. Let $E(\theta, v, s)$ be an internal energy and $C(\theta, v, s)$ a cost, both twice continuously differentiable, and for a real scalar $\beta$ (the *influence parameter*) define the total energy

$$F(\theta, v, \beta, s) = E(\theta, v, s) + \beta\, C(\theta, v, s).$$

Assume that for $\beta$ in a neighbourhood of $0$ there is a fixed point $s^{\beta}_{\theta,v}$ with

$$\frac{\partial F}{\partial s}\big(\theta, v, \beta, s^{\beta}_{\theta,v}\big) = 0, \qquad \frac{\partial^2 F}{\partial s^2}\big(\theta, v, \beta, s^{\beta}_{\theta,v}\big) \succ 0,$$

so that, by the implicit function theorem, $(\theta, \beta) \mapsto s^{\beta}_{\theta,v}$ is differentiable. Call $s^0_{\theta,v}$ the *free* fixed point and $s^{\beta}_{\theta,v}$ the *nudged* fixed point, and let the training objective be the cost at the free fixed point,

$$J(\theta, v) = C\big(\theta, v, s^0_{\theta,v}\big).$$

**Theorem.** The gradient of $J$ is

$$\frac{\partial J}{\partial \theta}(\theta, v) = \lim_{\beta \to 0} \frac{1}{\beta}\left( \frac{\partial F}{\partial \theta}\big(\theta, v, \beta, s^{\beta}_{\theta,v}\big) - \frac{\partial F}{\partial \theta}\big(\theta, v, 0, s^{0}_{\theta,v}\big) \right),$$

equivalently

$$\frac{\partial J}{\partial \theta}(\theta, v) = \frac{\partial C}{\partial \theta}\big(\theta, v, s^0_{\theta,v}\big) + \lim_{\beta \to 0} \frac{1}{\beta}\left( \frac{\partial E}{\partial \theta}\big(\theta, v, s^{\beta}_{\theta,v}\big) - \frac{\partial E}{\partial \theta}\big(\theta, v, s^{0}_{\theta,v}\big) \right).$$

The sign of $\beta$ is irrelevant; only $\beta \to 0$ is needed.

**Hopfield instance.** For units $u = (x, s)$ with activation $\rho$, symmetric weights $W_{ij} = W_{ji}$ and biases $b_i$, take

$$E(u) = \tfrac12 \sum_i u_i^2 - \tfrac12 \sum_{i \ne j} W_{ij}\,\rho(u_i)\rho(u_j) - \sum_i b_i\, \rho(u_i), \qquad C = \tfrac12 \lVert y - d \rVert^2,$$

with $y$ the output units. Then $\partial E / \partial W_{ij} = -\rho(u_i)\rho(u_j)$ and the theorem gives the local update

$$\Delta W_{ij} \propto \frac{1}{\beta}\Big( \rho(u^{\beta}_i)\rho(u^{\beta}_j) - \rho(u^{0}_i)\rho(u^{0}_j) \Big),$$

a contrastive Hebbian rule between the free and the weakly clamped equilibria.

## Proof depends on

- [Implicit function theorem](../../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md)

## Expansion

Differentiate the identity $\partial_s F(\theta, v, \beta, s^{\beta}_{\theta,v}) = 0$ and use the symmetry of mixed second derivatives: both $\frac{d}{d\beta}\partial_\theta F(\theta,v,\beta,s^\beta)\big|_{\beta=0}$ and $\frac{d}{d\theta} \partial_\beta F(\theta,v,\beta,s^\beta)\big|_{\beta=0}$ equal $\partial_\theta\partial_\beta F + \partial_s\partial_\theta F\cdot \partial_\beta s$-type terms that coincide once the fixed-point condition removes the $\partial_s F$ contributions. Since $\partial_\beta F(\theta, v, 0, s^0) = C(\theta, v, s^0) = J(\theta, v)$, the right-hand side is $\partial_\theta J$. The free phase relaxes the network to $s^0$; the nudged phase adds the external force $\beta(d - y)$ on the output units and relaxes to $s^\beta$, propagating error information backward through the same symmetric connections. With $E$ the Hopfield energy, $-\partial E/\partial s_i = \rho'(s_i)\big(\sum_{j \ne i} W_{ij}\rho(u_j) + b_i\big) - s_i$, which is a leaky-integrator neuron model.

## Sources

- B. Scellier, Y. Bengio, "Equilibrium Propagation: Bridging the Gap between Energy-Based Models and Backpropagation", Frontiers in Computational Neuroscience 11:24 (2017), Section 2 (Hopfield energy, Eq. 1; cost, Eq. 2; total energy, Eq. 3; neural dynamics, Eq. 8), Section 3.2–3.3 (Eqs. 20–21, Theorem 1, Eqs. 22–24) and Appendix A (proof), <https://doi.org/10.3389/fncom.2017.00024> (PMC5415673).
