# Degree-based mean-field threshold of the activity-driven SIS epidemic

In the discrete-time **activity-driven SIS (A-SIS) epidemic** on $n$ nodes, at each step every node activates with a probability that depends on its degree class $d \in \mathcal{D}$ and on its state: $\pi_{d,S}$ when susceptible, $\pi_{d,X}$ when infected. An active node of degree $d$ connects to $d$ uniformly chosen other nodes. Infection passes along each such edge with probability $\beta$, and an infected node recovers with probability $\delta$. Let $m_d$ be the fraction of nodes of degree $d$, $\bar d = d/(n-1)$, and let $x_d(k)$ be the infected fraction in class $d$. The degree-based mean-field (DBMF) approximation is

$$
x_d(k+1) = (1-\delta) x_d(k) + (1 - x_d(k)) \sum_{t \in \mathcal{D}} n m_t \beta \big[ 1 - (1 - \pi_{d,S}\bar d)(1 - \pi_{t,X}\bar t) \big] x_t(k).
$$

**Proposition.** Let $\delta, \beta \in (0,1]$, let the activation probabilities $\pi_{d,S}, \pi_{d,X} \in (0,1]$ be constant in time, and assume $\beta(d_{avg} + d_{max}) \le 1$. Define $F \in \mathbb{R}^{|\mathcal{D}| \times |\mathcal{D}|}$ by

$$
F_{d,t} = \delta_{dt}(1 - \delta) + n m_t \beta \big[ 1 - (1 - \pi_{d,S}\bar d)(1 - \pi_{t,X}\bar t) \big],
$$

where $\delta_{dt}$ is the Kronecker delta. Then $[0,1]^{|\mathcal{D}|}$ is invariant, and:

1. if $\rho(F) \le 1$, the disease-free state $x = 0$ is the unique equilibrium and attracts all of $[0,1]^{|\mathcal{D}|}$;
2. if $\rho(F) > 1$, there are exactly two equilibria, $0$ and an endemic $x^*$ with $x^*_d > 0$ for all $d$. If moreover $\delta + \beta(d_{avg} + d_{max}) \le 1$, then $x^*$ attracts $[0,1]^{|\mathcal{D}|} \setminus \{0\}$.

## Depends on

- [Spectral radius and die-out of SIS epidemics](../../sis-extinction-times-on-finite-graphs/prob-ne-empty-le.md)

## Expansion

The individual-based mean-field equations come from the exact Markov chain: assume the states of distinct nodes are independent, and linearize the probability of escaping infection with the Weierstrass product inequality. Aggregating identical nodes by degree gives the DBMF map, which has the same form as the discrete-time networked SIS model $x(k+1) = x + h[(I-X)Bx - Dx]$ with an effective infection matrix. The known threshold theorem for that model (Paré et al.; Liu et al.) then applies, and $F$ is its Jacobian at the disease-free state.

## Sources

- Ashish R. Hota, Tanya Sneh, Kavish Gupta, "Impacts of Game-Theoretic Activation on Epidemic Spread over Dynamical Networks", SIAM Journal on Control and Optimization 60 (2022), S92–S118, <https://doi.org/10.1137/20m1376923>. Published version of arXiv:2011.00445, cited next; locators there refer to the arXiv version.
- Ashish R. Hota, Tanya Sneh, Kavish Gupta, "Impacts of Game-Theoretic Activation on Epidemic Spread over Dynamical Networks", arXiv (2020). Section "A-SIS Epidemic under Game-Theoretic Activation": individual-based mean-field theorem for the A-SIS model, DBMF definition and the spectral-radius proposition; appendix theorem on discrete-time networked SIS. <https://doi.org/10.48550/arXiv.2011.00445>
