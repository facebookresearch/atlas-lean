# Global stability of an epidemic population game with disease deaths

**Strategic population.** A large population chooses among $n$ strategies. Strategy $\ell$ yields transmission rate $\vec\beta_\ell$ and inherent cost $c_\ell$, ordered so that $\vec\beta_1<\dots<\vec\beta_n$ and $c_1>\dots>c_n$. Write $\tilde c_i = c_i - c_n$. The population state $x$ lies in the simplex $\mathbb X$, and the aggregate transmission rate is $\mathcal B = \vec\beta^{T}x$. Strategies evolve by an evolutionary dynamics model

$$
\dot x_i = \sum_{j\ne i} x_j\,\mathcal T_{ji}(x,p) - \sum_{j\ne i} x_i\,\mathcal T_{ij}(x,p),
$$

driven by a bounded Lipschitz revision protocol $\mathcal T$ and payoff vector $p$. Two assumptions on the protocol are used:

- *Nash stationarity*: $\dot x = 0$ iff $x$ is a best response to $p$.
- *$\delta$-passivity with homogeneity*: there are a storage function $\mathcal S(x,p)\ge 0$ and a dissipation $\mathcal P(x,p)\ge 0$, both vanishing exactly at rest points, with $\partial_x\mathcal S\,\dot x + \partial_p\mathcal S\,u\le -\mathcal P + u^{T}\dot x$ for all $u$, and $\mathcal P(x,\alpha p)\ge\mathcal P(x,p)$ for $\alpha\ge 1$.

Every impartial pairwise comparison protocol with nondecreasing switching rates, such as Smith's protocol, satisfies both.

**Epidemic.** The infectious and recovered fractions follow the normalized SIRS model with disease death rate $\delta$ ([Lyapunov function for the normalized SIRS model with disease mortality](lyapunov-function-for-the-normalized-sirs-model-with-disease-mortality.md)) with transmission rate $\mathcal B(t)$. Assume $\delta<\omega$, $\delta<\gamma$ and $\sigma<\vec\beta_1$. Also assume the marginal costs are increasing as transmission falls: $\frac{c_i - c_{i+1}}{\vec\beta_{i+1} - \vec\beta_i} > \frac{c_{i+1} - c_{i+2}}{\vec\beta_{i+2} - \vec\beta_{i+1}}$ for $n\ge 3$.

**Planner.** Fix a budget $c^*\in(0,\tilde c_1)\setminus\{\tilde c_n,\dots,\tilde c_1\}$. Let $x^* = \arg\min\{\vec\beta^{T}x : \tilde c^{T}x\le c^*,\ x\in\mathbb X\}$, which is unique and supported on two adjacent strategies, and set $\beta^* = \vec\beta^{T}x^*$. Payoffs are $p = q\vec\beta + r^* - c$, where the scalar incentive $q$ evolves as $\dot q = G(I,R,x,q)$ and $r^*$ is chosen per strategy ($r^*_i = \tilde c_i$, except $r^*_i<\tilde c_i$ for strategies unused by $x^*$ when $n>2$). The policy is $G = -\partial_{\mathcal B}\mathscr S$, where

$$
\mathscr S(I,R,\mathcal B) = \hat I_{\mathcal B}\ln\frac{\hat I_{\mathcal B}}{I} - (\hat I_{\mathcal B} - I) + \frac{a_{\mathcal B}}{2}(\hat R_{\mathcal B} - R)^2 + \frac{\upsilon^2}{2}(\mathcal B - \beta^*)^2,
$$

with $a_{\mathcal B} = \mathcal B/(\gamma + \delta\hat R_{\mathcal B})$, $(\hat I_{\mathcal B},\hat R_{\mathcal B})$ the endemic equilibrium at transmission rate $\mathcal B$, and a design gain $\upsilon>0$.

**Theorem.** Under these assumptions, the equilibrium $e^* = (I^*,R^*,x^*,0)$ of the coupled evolutionary-dynamics and epidemic system is globally asymptotically stable on $\mathbb Y = \{0<I\le 1,\ 0\le R\le 1-I\}\times\mathbb X\times\mathbb R$. Consequently $(I,R,x,q,\mathcal B)(t)\to(I^*,R^*,x^*,0,\beta^*)$ and the planner's running cost $r(t)^{T}x(t)\to c^*$. The endemic infection level converges to the lowest one achievable with long-run average cost $c^*$, without the planner knowing the protocol.

## Depends on

- [Lyapunov function for the normalized SIRS model with disease mortality](lyapunov-function-for-the-normalized-sirs-model-with-disease-mortality.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

The Lyapunov candidate is $\mathcal L = \mathscr S(I,R,\mathcal B) + \mathcal S(x,p)$. With $G = -\partial_{\mathcal B}\mathscr S$, the $\mathcal B$-dependence of $\mathscr S$ is offset by the passivity supply term, and

$$
\frac{d}{dt}\mathcal L \le -\mathcal P(x,p) - (\mathcal B - \delta)(\hat I_{\mathcal B} - I)^2 - a_{\mathcal B}(\omega - \delta I)(\hat R_{\mathcal B} - R)^2 .
$$

The last two terms vanish only on the moving endemic curve, and $\mathcal P$ vanishes only at rest points of the strategy dynamics. A LaSalle-type argument then shows that $e^*$ is the unique accumulation point, provided $q$ stays bounded. Boundedness comes from uniform bounds on $\partial_{\mathcal B}\hat I_{\mathcal B}$, $\partial_{\mathcal B}\hat R_{\mathcal B}$, $a_{\mathcal B}$ and $\ln\hat I_{\mathcal B}$ for $\mathcal B\in[\vec\beta_1,\vec\beta_n]$. The positive death rate couples $I$ and $R$ through $\delta RI$, which is why $a_{\mathcal B}$ depends on $\hat R_{\mathcal B}$. The same $\mathcal L$ also yields anytime upper bounds on the infectious fraction, computed to arbitrary accuracy by solving convex programs.

## Sources

- Jair Certorio, Nuno C. Martins, Richard J. La, "Epidemic Population Games With Nonnegligible Disease Death Rate", IEEE Control Systems Letters 6 (2022), 3229–3234, <https://doi.org/10.1109/lcsys.2022.3183477>. Published version of arXiv:2204.00953, cited next; locators there refer to the arXiv version.
- Jair Certório, Nuno C. Martins, Richard J. La, "Epidemic Population Games With Nonnegligible Disease Death Rate", arXiv 2022: Section II (evolutionary dynamics model, Definition 1, Assumptions 1–2), Section III (Assumptions 3–4, Definition 2), Section IV (the stabilizing policy $G$, Definition 3, Theorem 1). <https://doi.org/10.48550/arXiv.2204.00953>
