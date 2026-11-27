# Stationary distributions of stochastic May–Leonard models

**Mean-field model.** Three competing species with counts $N_1, N_2, N_3$, system size $\Omega > 0$ and cyclic competition coefficients $\alpha, \beta$ (indices mod $3$) follow

$$\frac{dN_i}{dt} = N_i\Big(r - \frac{N_i}{\Omega} - \frac{\alpha}{\Omega} N_{i+1} - \frac{\beta}{\Omega} N_{i+2}\Big),$$

which for $\alpha + \beta > 2$ with $\alpha < 1$ or $\beta < 1$ exhibits May–Leonard heteroclinic cycling between the single-species states. Demographic noise is introduced by a stochastic mass-action reaction network on $\mathbb Z_{\ge 0}^3$ with reactions, for each $i$,

$$A_i \xrightarrow{b} 2A_i, \qquad 2A_i \xrightarrow{2/\Omega} A_i, \qquad A_i + A_{i+1} \xrightarrow{\alpha/\Omega} A_{i+1}, \qquad A_i + A_{i+2} \xrightarrow{\beta/\Omega} A_{i+2},$$

plus, in the **general variance model**, individual death $A_i \xrightarrow{d} \emptyset$ with $b - d = r > 0$. The **minimal model** has no individual death and $b = r$. Both have the same mean-field limit.

**Proposition 1 (total extinction).** In the general variance model with $d > 0$, the unique stationary distribution is $\pi = \delta_{(0,0,0)}$: all three species go extinct with probability one from every initial condition.

**Proposition 2 (single-species persistence).** The minimal model has exactly four stationary distributions: $\delta_{(0,0,0)}$ and, for each $i \in \{1,2,3\}$,

$$\pi(N) = \frac{(r\Omega)^{N_i}}{N_i!\,\big(e^{r\Omega} - 1\big)}\ \delta(N_{i+1})\,\delta(N_{i+2}), \qquad N_i \ge 1,$$

a zero-truncated Poisson law of mean parameter $r\Omega$ for the surviving species, the others being extinct.

## Expansion

With individual deaths, the origin is reachable from every state and absorbing, and the chain is irreducible on the rest, so all stationary mass sits at extinction even though the deterministic model never reaches it; this mirrors the classical contrast between mean-field equilibria and stochastic extinction. Without individual deaths, a lone species can only lose individuals by pairwise homocidal competition, which needs two individuals, so the state with one survivor and zero for the others is a closed class that never reaches $0$. On that one-dimensional class the birth rate $rN$ and death rate $N(N-1)/\Omega$ satisfy detailed balance $\pi(N+1)/\pi(N) = r\Omega/(N+1)$, which yields the truncated Poisson law; equivalently it is the complex-balanced product-form distribution of Anderson and Kurtz restricted to the closed class. Two species go extinct quickly in both models, and only the death mechanism decides whether the third persists, showing that the long-time behavior of noisy heteroclinic cycles depends on the microscopic noise model, not only on the mean-field equations.

## Sources

- N. W. Barendregt, P. J. Thomas, "Heteroclinic cycling and extinction in May-Leonard models with demographic stochasticity", Journal of Mathematical Biology 86(2) (2023) 30, Equations (3)-(15), Propositions 1-2 with proofs in Appendices B-C, <https://doi.org/10.1007/s00285-022-01859-4>, PMCID PMC9839821.
