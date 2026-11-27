# Mean ergodicity of seasonal piecewise-deterministic savanna models

**Model.** Normalized woody and grass biomasses $w, g \in [0,1]$ follow, between fires,

$$\frac{dw}{dt} = r_w^i\,w(1 - w), \qquad \frac{dg}{dt} = r_g^i\,g(1 - g - w),$$

where $i \in \{0,1\}$ is the current season (dry/wet), which alternates deterministically with fixed season lengths. Fires occur at rate $\lambda^i(w, g, \zeta)$ depending on biomass, season and the time $\zeta$ elapsed in the current season; at a fire, biomasses lose random fractions with season-dependent laws, $w \mapsto w - M_w w$, $g \mapsto g - M_g g$. Adding herbivore (grazer and browser) compartments gives a four-dimensional variant. The state $(\xi, \zeta, i)$ forms a piecewise-deterministic Markov process (PDMP) $\Phi$ with parameters switching at fixed periods.

**Theorem (mean ergodicity).** Under regularity assumptions on the rates and loss distributions (and a condition keeping biomass away from extinction), for each initial state $x$ there is a probability measure $\Pi(x,\cdot)$ with

$$\lim_{t\to\infty}\frac1t\int_0^t\mathbb P_x(\Phi(s) \in B)\,ds = \Pi(x,B)$$

for every Borel set $B$, and for every bounded measurable $f$

$$\mathbb P_x\Big(\lim_{t\to\infty}\frac1t\int_0^tf(\Phi(s))\,ds = \int f\,d\tilde\Pi\Big) = 1,$$

for a random measure $\tilde\Pi$ with $\Pi(x,B) = \mathbb E_x\tilde\Pi(B)$. If the invariant probability measure is unique, the Cesàro averages converge in total variation and time averages converge a.s. to $\int f\,d\pi$.

**Corollary (fire losses proportional to biomass).** If losses are constant fractions $M_w^i, M_g^i$ and the fire rate is $\lambda^i = \lambda_0^ig$ with $\lambda_0^i > 0$, the persistence condition holds whenever

$$r_w^i + \lambda_0^i\ln(1 - M_w^i) > 0, \qquad i = 0, 1,$$

i.e. the mean logarithmic growth rate of woody biomass stays positive in each season despite fire losses.

## Proof sketch

The general result is a criterion for continuous-time Markov processes: a Foster–Lyapunov-type drift condition (V) excluding escape to the boundary plus the $T$-process property (a continuous component in the resolvent) imply mean ergodicity, via the embedded chain sampled at the jump times. For the savanna PDMP the drift condition comes from the logarithmic growth of $w$ between fires against the expected log-loss at fires, which is where $r_w + \lambda_0\ln(1 - M_w) > 0$ appears, and the $T$-property comes from the randomness of fire times and losses. Seasonality makes the dynamics time-inhomogeneous, handled by including the time within the season as a state variable.

## Sources

- Paweł Klimasara and Marta Tyran-Kamińska, "A Model of Seasonal Savanna Dynamics", *SIAM Journal on Applied Mathematics* 83 (2023), 122–143, <https://doi.org/10.1137/21m1461393>. Preprint version: arXiv:2211.05859 (2022), Sections 2–3 (models), Theorem 4.1 and Corollary 4.2 (Section 4), Theorem 5.1, Corollary 5.2 and Theorem 5.3 (Section 5), <https://doi.org/10.48550/arXiv.2211.05859>.
