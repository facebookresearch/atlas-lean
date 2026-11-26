# Message passing and edge-based models for non-Markovian SIR

**Setting.** An SIR epidemic spreads on a configuration-model network with degree distribution $(p_k)$ and mean degree $\langle k\rangle$. A node infected at age $a = 0$ attempts transmission to each neighbour after a time with density $\tau(a)$ and recovers after a time with density $q(a)$, independently, with survival functions $\xi_\tau(a) = \int_a^\infty \tau$, $\xi_q(a) = \int_a^\infty q$ and hazards $\zeta = \tau/\xi_\tau$, $\rho = q/\xi_q$. A fraction $1 - z$ of nodes is infected at time $0$. Let

$$G_0(x) = \sum_k p_k x^k, \qquad G_1(x) = \frac{1}{\langle k\rangle}\sum_k k p_k x^{k-1}, \qquad G_2 = G_1',$$

and let $f(a) = \tau(a)\,\xi_q(a)$ be the density of the age at which a transmission attempt along an edge happens before recovery; $T = \int_0^\infty f$ is the transmissibility.

**Message-passing (MP) model.** Let $H_1(t)$ be the probability that a random neighbour of a test node (held in a cavity state, unable to transmit) has not attempted to transmit to it by time $t$. On the locally tree-like infinite network,

$$H_1(t) = 1 - \int_0^t f(a)\Big(1 - z\,G_1\big(H_1(t - a)\big)\Big)\,da, \qquad H_1(0) = 1,$$

and

$$S(t) = z\,G_0\big(H_1(t)\big), \qquad R(t) = \int_0^t q(a)\big(1 - S(t-a)\big)\,da, \qquad I = 1 - S - R .$$

In the Markovian case (rates $\beta, \gamma$) this reduces to $\dot H_1 = \gamma - (\beta + \gamma)H_1 + \beta z\, G_1(H_1)$.

**Edge-based compartmental model (EBCM).** With $\Theta(t)$ the probability that a random edge has not transmitted to the test node and $\phi_I(t, a)$ the density of infected neighbours of infection age $a$ that have not yet transmitted,

$$\dot\Theta = -\int_0^t \zeta(a)\phi_I(t,a)\,da, \qquad \phi_I(t, 0) = (1-z)\delta(t) + z\,G_2(\Theta)\int_0^t \zeta(a)\phi_I(t,a)\,da,$$

$$\Big(\partial_t + \partial_a\Big)\phi_I = -\big(\zeta(a) + \rho(a)\big)\phi_I, \qquad S(t) = z\,G_0(\Theta(t)),$$

with an analogous age-structured equation $(\partial_t + \partial_a) i = -\rho(a)\, i$ for infected nodes fed by $i(t,0) = -\dot S$.

**Theorem.** If $\tau$ and $q$ are independent integrable probability densities, the MP model and the EBCM are equivalent: $\Theta(t) = H_1(t)$ and both produce identical $S, I, R$ trajectories for shared initial conditions. In particular the EBCM is exact for the stochastic epidemic on the ensemble of infinite configuration-model networks.

## Expansion

$1 - H_1(t)$ is the probability that the neighbour has been infected at some time $t_1$ and has then made its attempt within $t - t_1$: either it was initially infected (probability $1 - z$), or it was susceptible and was infected through one of its other edges, which on a tree happens independently with probability $1 - G_1(H_1)$ at the relevant time; integrating over the attempt age with density $f$ gives the renewal equation. In the EBCM, solving the transport equation along characteristics gives $\phi_I(t,a) = \phi_I(t-a,0)\,\xi_\tau(a)\xi_q(a)$, so $\int_0^t\zeta\phi_I = \int_0^t f(a)\phi_I(t-a,0)\,da$; substituting $\phi_I(\cdot,0) = -\dot\Phi_S$ with $\Phi_S = zG_1(\Theta)$ and integrating $\dot\Theta$ reproduces the MP equation for $H_1$. Specialising to regular networks, exponential, or fixed-length infectious periods recovers known pairwise models, including delay-differential pairwise models.

## Sources

- N. Sherborne, J. C. Miller, K. B. Blyuss, I. Z. Kiss, "Mean-field models for non-Markovian epidemics on networks", Journal of Mathematical Biology 76 (2018) 755–778, Section 2 (Eq. 1; MP model, Eqs. 2–5; hazards, Eq. 6; EBCM, Eqs. 8a–8k; Theorem 1 with proof) and Section 3 (model hierarchy), <https://doi.org/10.1007/s00285-017-1155-0> (PMC5772140).
- B. Karrer, M. E. J. Newman, "Message passing approach for general epidemic models", Physical Review E 82 (2010) 016101, <https://doi.org/10.1103/PhysRevE.82.016101>.
