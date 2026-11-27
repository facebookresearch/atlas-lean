# Dynamic payoff mechanism steering an SIRS epidemic population game to the optimal endemic equilibrium

**Epidemic population game.** A large population chooses among strategies $1, \dots, n$ with transmission levels $\beta_1 < \dots < \beta_n$ and intrinsic costs $c_1 > \dots > c_n$ (safer strategies cost more), $\beta_1 > \sigma$. The population state $x(t)$ lies in the simplex $\mathbb{X}$, the transmission rate is $\mathcal{B}(t) = \beta^\top x(t)$, and with normalized SIRS variables

$$ \dot I = \bigl( \mathcal{B} (1 - I - R) - \sigma \bigr) I, \qquad \dot R = \gamma I - \omega R, \qquad \dot q = G(I, R, x, q), \qquad r = H(I, R, x, q), $$

where $r$ is a reward vector set by a planner through an internal state $q$. Agents revise strategies by an evolutionary dynamics model $\dot x_i = \sum_{j \ne i} x_j \mathcal{T}_{ji}(x, p) - x_i \sum_{j \ne i} \mathcal{T}_{ij}(x, p)$ driven by the payoff $p = r - c$, for a Lipschitz revision protocol $\mathcal{T}$ (for example impartial pairwise comparison protocols such as Smith's, $\mathcal{T}_{ij} = \min\{\lambda [p_j - p_i]_+, \bar{\mathcal{T}}\}$).

Given a budget $c^* \in (0, \tilde c_1)$, $\tilde c_i = c_i - c_n$, the optimal endemic transmission rate and its unique minimizer (under the convexity condition $\frac{c_i - c_{i+1}}{\beta_{i+1} - \beta_i} > \frac{c_{i+1} - c_{i+2}}{\beta_{i+2} - \beta_{i+1}}$) are

$$ \beta^* = \min\{ \beta^\top x : \tilde c^\top x \le c^*,\ x \in \mathbb{X} \}, \qquad I^* = \eta\Bigl(1 - \frac{\sigma}{\beta^*}\Bigr), \quad R^* = (1 - \eta)\Bigl(1 - \frac{\sigma}{\beta^*}\Bigr), \quad \eta = \frac{\omega}{\omega + \gamma}. $$

**Mechanism.** With reference values $\hat I = \eta(1 - \sigma/\mathcal{B})$, $\hat R = (1 - \eta)(1 - \sigma/\mathcal{B})$ and design parameters $\upsilon > 0$, $\rho^* > 0$, take

$$ G = (\hat I - I) + \eta (\ln I - \ln \hat I) + \upsilon^2 (\beta^* - \mathcal{B}) + \frac{\mathcal{B}}{\gamma} (R - \hat R)(1 - \eta - R), \qquad H = q \beta + r^*, $$

where $r^*_i = \tilde c_i - \rho^*$ if $x^*_i = 0$ and $r^*_i = \tilde c_i$ otherwise.

**Theorem 1.** Suppose the protocol is Nash stationary ($\mathcal{V}(x,p) = 0$ exactly when $x$ is a best response to $p$) and $\delta$-passive, and $\rho^*$ is chosen validly. Then the set $\mathbb{E}^* = (I^*, R^*, x^*) \times \mathfrak{Q}^*$, with $\mathfrak{Q}^* = \{0\}$ when $c^*$ lies strictly between consecutive $\tilde c_i$ and $\mathfrak{Q}^* = [-\rho^*/(\beta^* - \beta_1), \rho^*/(\beta_n - \beta^*)]$ when $c^* = \tilde c_{i^*}$, is globally asymptotically stable for the closed loop. Consequently, from every initial condition with $I(0) > 0$, $(I, R, \mathcal{B})(t) \to (I^*, R^*, \beta^*)$, and $\limsup_{t \to \infty} x(t)^\top r(t) \le c^*$ when $c^*$ lies strictly between consecutive $\tilde c_i$, while $\limsup_{t \to \infty} x(t)^\top r(t) \le c^* + \rho^*\beta^*/(\beta_n - \beta^*)$ when $c^* = \tilde c_{i^*}$: the epidemic settles at the smallest endemic infectious fraction affordable within the long-run average incentive budget.

## Expansion

The design is built backwards from a Lyapunov function for the coupled system: a logarithmic (Volterra-type) term in $I$ relative to the reference $\hat I$, a quadratic term in $R - \hat R$, a quadratic term in the planner state $q$, and the $\delta$-passivity storage function $\mathcal{S}$ of the evolutionary dynamics, which certifies that the population's strategy revision does not create energy when payoffs change. The specific $G$ cancels the cross terms between the epidemic and the payoff dynamics, so the total function is non-increasing along trajectories, and Nash stationarity together with the uniqueness of $x^*$ as the best response to $r^* - c$ with $\beta^\top x^* = \beta^*$ identifies $\mathbb{E}^*$ as the largest invariant set where it stops decreasing. Because the Lyapunov function is explicit, its initial value also yields anytime upper bounds on the peak infectious fraction $I(t)$, addressing the overshoot that arises when $\mathcal{B}$ is used directly as a control.

## Sources

- Nuno C. Martins, Jair Certório, Richard J. La, "Epidemic population games and evolutionary dynamics", Automatica 153 (2023), 111016, <https://doi.org/10.1016/j.automatica.2023.111016>. Published version of arXiv:2201.10529, cited next; locators there refer to the arXiv version.
- Nuno C. Martins, Jair Certorio, Richard J. La, "Epidemic Population Games And Evolutionary Dynamics", arXiv (2022). Section 1 (EDM, EPG, Definition of $\beta^*$), Section 3 (Assumptions 1-2, choice of $G$ and $H$, Theorem 1) and Section 4 (anytime bounds). <https://doi.org/10.48550/arXiv.2201.10529>
