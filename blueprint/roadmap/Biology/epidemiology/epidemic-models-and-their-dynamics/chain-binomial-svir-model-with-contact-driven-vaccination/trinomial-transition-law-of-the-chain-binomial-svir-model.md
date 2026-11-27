# Trinomial transition law of the chain-binomial SVIR model

**Model.** A closed population of $n$ individuals is observed at integer times. Vaccine-induced immunity lasts a fixed $T_1$ time units (after which vaccinated individuals return to the susceptible class), infectiousness lasts a fixed $T_2$ time units, and recovery gives permanent immunity. The state $B(t)$ records the susceptibles $S(t)$ together with the vaccinated and infectious individuals stratified by time since vaccination or infection. Assume homogeneous mixing; each susceptible makes $N$ contacts per time step, each contact being with an infectious individual with probability $I(t-1)/(n-1)$, independently; each contact with an infectious individual transmits independently with probability $p$; and a susceptible who meets infectious individuals but is not infected seeks vaccination within the step with probability $\phi$.

**Theorem.** For $t \ge \max\{T_1, T_2\}$, $\{B(t)\}$ is a Markov chain. For each susceptible, the probabilities of infection and of vaccination in the step ending at time $t$ are

$$P_I(t) = 1 - \Bigl(1 - \frac{p\, I(t-1)}{n-1}\Bigr)^{N}, \qquad P_V(t) = \phi \Bigl[\Bigl(1 - \frac{p\, I(t-1)}{n-1}\Bigr)^{N} - \Bigl(1 - \frac{I(t-1)}{n-1}\Bigr)^{N}\Bigr],$$

and $P_S(t) = 1 - P_I(t) - P_V(t)$. The source's (4.6) prints $P_V(t)=\phi(1-pI(t-1)/(n-1))^N$; this page differs because that expression drops the $j=0$ term of the source's own sum (4.5), which runs over $j\ge1$ infectious contacts: with $q=I(t-1)/(n-1)$, $\sum_{j\ge1}\binom Nj q^j(1-q)^{N-j}(1-p)^j=(1-pq)^N-(1-q)^N$. Given $S(t) = x_t$, the numbers $y$ newly vaccinated and $z$ newly infected at time $t+1$ (with $x_{t+1} = x_t - y - z$ remaining susceptible) have the trinomial law

$$\mathbb{P}\bigl(V_0(t+1) = y,\ I_0(t+1) = z \mid B(t)\bigr) = \binom{x_t}{y} \binom{x_t - y}{z} P_V^{\,y}\, P_I^{\,z}\, P_S^{\,x_t - y - z},$$

so that the newly vaccinated and newly infected counts are each binomial with success probabilities $P_V$ and $P_I$. Consequently, while all infectious individuals are still within their infectious period,

$$\mathbb{E}[I(t) \mid B(0)] = I_0(0) + \sum_{k=1}^{t-1} \mathbb{E}\Bigl[ S(t-k-1)\Bigl(1 - \Bigl(1 - \frac{p\, I(t-k-1)}{n-1}\Bigr)^{N}\Bigr) \Bigm| B(0) \Bigr],$$

and the expected number infected over one infectious period, evaluated at $t = T_2$, defines the basic reproduction number of the model implicitly.

**Poisson-contact variant.** If instead the number of contacts per step is Poisson with mean $\lambda$ and susceptibles are vaccinated independently at constant rate $\mu_v$, the same trinomial law holds with

$$P_I(t) = 1 - \exp\Bigl(-\frac{p \lambda\, I(t-1)}{n-1}\Bigr), \qquad P_V(t) = 1 - e^{-\mu_v}.$$

## Expansion

The infection probability comes from conditioning on the number $j$ of infectious contacts, which is binomial with parameters $N$ and $I(t-1)/(n-1)$, and using $1 - (1-p)^j$ for the chance that at least one of them transmits; the binomial theorem collapses the sum to $1 - (1 - p I/(n-1))^N$. A susceptible who escapes infection after at least one infectious contact is vaccinated with probability $\phi$, and the probability of at least one infectious contact without infection is $\sum_{j\ge1}\binom Nj q^j(1-q)^{N-j}(1-p)^j=(1-pq)^N-(1-q)^N$ with $q=I(t-1)/(n-1)$; the vaccine is assumed to reverse any infection acquired within the same step. Because susceptibles act independently and each has three possible outcomes, the joint law of the outcomes is trinomial, and its margins are binomial. Fixed sojourn times make the age-stratified state Markov. The model reduces to a Reed–Frost chain binomial when $\phi = 0$ and each susceptible contacts everyone.

## Sources

- Divine Wanduku, "On a family of stochastic SVIR influenza epidemic models and maximum likelihood estimation", arXiv (2019). Theorem 3.1, Theorem 4.1, Lemma 4.1, Theorem 4.2, Theorem 6.1, Corollary 6.1. <https://doi.org/10.48550/arXiv.1901.05315> Published version: D. Wanduku, C. Newman, O. Jegede, B. Oluyede, "Modeling the stochastic dynamics of influenza epidemics with vaccination control, and the maximum likelihood estimation of model parameters", in Mathematical Modelling in Health, Social and Applied Sciences, Forum for Interdisciplinary Mathematics, Springer (2020) 23–72, <https://doi.org/10.1007/978-981-15-2286-4_2>.
