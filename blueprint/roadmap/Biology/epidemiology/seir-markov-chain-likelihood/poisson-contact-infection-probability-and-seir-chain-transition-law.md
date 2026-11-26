# Poisson-contact infection probability and the SEIR chain transition law

**Model.** A closed population of size $N$ is observed at times $t_k = k\Delta t$ in states $X(t_k) = (S,E,I,R)(t_k)$. Assume:
1. a susceptible meets other individuals according to a Poisson process of rate $\lambda$, so the number of contacts in one epoch is $\mathrm{Poisson}(\lambda\Delta t)$;
2. each contact is with an infectious person with probability $\alpha^i(t_k) = I(t_k)/(N-1)$, independently;
3. each contact with an infectious person transmits with probability $p$.

**Theorem.**
1. (Infection probability) With no births or deaths, the probability that a given susceptible becomes infected during epoch $k$ is
$$p^i(t_k) = 1 - e^{-p\,\alpha^i(t_k)\,\lambda\,\Delta t}.$$
2. (Transition law with unit incubation and infectious periods) If in addition the incubation and infectious periods are constant and equal to $\Delta t$, then $\{X(t_k)\}$ is a Markov chain with
$$\mathbb{P}\big(X(t_{k+1}) = x^{k+1} \mid X(t_k) = x^k\big) = \binom{s_k}{s_{k+1}}\big(p^i(t_k)\big)^{s_k - s_{k+1}}\big(1 - p^i(t_k)\big)^{s_{k+1}}$$
on the feasible set $\{s_{k+1} + e_{k+1} = s_k,\ i_{k+1} = e_k,\ 0 \le s_{k+1}, e_{k+1}, i_{k+1} \le s_k\}$, and $0$ elsewhere: new exposures are $\mathrm{Binomial}(s_k, p^i(t_k))$, exposed individuals become infectious after one step and infectious individuals are removed after one step.
3. (General case) With births, deaths, or random incubation and infectious periods, $X(t_k)$ is still a discrete-time Markov chain whose transition probabilities are products of the laws of the conversion counts $C_{SE}$, $C_{EI}$, $C_{IR}$ and of births and deaths; for Poisson conversions with rates $\delta_e$, $\delta_r$ these factors are explicit.

## Expansion

The number of infectious contacts is a Poisson thinning: $\mathrm{Poisson}(\lambda\Delta t)$ contacts, each infectious with probability $\alpha^i$ and transmitting with probability $p$, give $\mathrm{Poisson}(p\alpha^i\lambda\Delta t)$ transmitting contacts, and escape means zero of them, probability $e^{-p\alpha^i\lambda\Delta t}$. Independence across susceptibles yields the binomial chain, a Reed-Frost-type model with an exponential rather than power escape probability. The explicit transition law makes the complete-data likelihood of an observed trajectory a product of binomial terms, so $p$ (and the conversion rates) can be estimated by maximum likelihood, with the expectation-maximization algorithm handling unobserved compartments.

## Sources

- Divine Wanduku and Chinmoy Rahul, "Complete maximum likelihood estimation for SEIR epidemic models: theoretical development", arXiv:1907.10679 (2019), Section 2 (Theorems 2.1 and 2.2), Section 3 (Assumption 3.1, Theorems 3.1-3.3) and Section 4 (Theorem 4.1), <https://doi.org/10.48550/arXiv.1907.10679>.
