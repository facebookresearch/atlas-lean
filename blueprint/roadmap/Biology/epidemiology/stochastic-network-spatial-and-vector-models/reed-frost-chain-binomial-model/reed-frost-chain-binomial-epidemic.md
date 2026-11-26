# Reed–Frost chain-binomial epidemic

**Model.** In a closed population, time advances in discrete generations $t = 0, 1, 2, \dots$ equal to the serial interval. Let $S_t$ and $I_t$ be the numbers susceptible and newly infected (infectious for exactly one generation) at generation $t$. Each infective independently makes adequate contact with each susceptible with probability $p \in (0,1)$, so a susceptible escapes infection in generation $t$ with probability $q^{I_t}$, $q = 1 - p$. Given $(S_t, I_t)$,

$$I_{t+1} \sim \mathrm{Binomial}\big(S_t,\ 1 - q^{I_t}\big), \qquad S_{t+1} = S_t - I_{t+1},$$

and $(S_t, I_t)$ is a Markov chain that stops when $I_t = 0$.

**Properties.**

1. *Chain probabilities.* The probability of a particular chain $i_0, i_1, \dots, i_T, 0$ starting from $s_0$ susceptibles is

$$\prod_{t=0}^{T}\binom{s_t}{i_{t+1}} \big(1 - q^{i_t}\big)^{i_{t+1}}\, q^{\,i_t s_{t+1}}, \qquad s_{t+1} = s_t - i_{t+1}, \quad i_{T+1} = 0 .$$

2. *Expected next generation.* $\mathbb{E}[I_{t+1} \mid S_t, I_t] = S_t(1 - q^{I_t})$, which for small $p$ is approximately $p\, S_t I_t$, the mass-action term of the discrete-time SIR model.
3. *Threshold.* With $N$ large and $p = \beta/N$, the number of secondary cases from one infective in a fully susceptible population is approximately Poisson with mean $R_0 = \beta S_0/N$, so a major outbreak has positive probability if and only if $R_0 > 1$ in the limit.

## Expansion

A susceptible escapes in generation $t$ only if it escapes each of the $I_t$ infectives independently, which gives $q^{I_t}$; independence across susceptibles gives the binomial law and hence the chain probability by the Markov property. The expectation in property 2 follows from the binomial mean, and $1 - (1-p)^{I} = pI + O(p^2 I^2)$. For property 3, one infective among $S_0 \approx N$ susceptibles infects $\mathrm{Binomial}(S_0, \beta/N) \to \mathrm{Poisson}(\beta S_0/N)$ others, and early generations form a Galton–Watson process. The Greenwood model is the variant in which the infection probability $1 - q$ does not depend on the number of infectives. The Reed–Frost model is the prototype of discrete-time stochastic epidemic models and of household final-size calculations.

## Sources

- Siettos CI, Russo L, "Mathematical modeling of infectious disease dynamics" (2013), Introduction (Enko and Reed–Frost chain binomial models as the basis of stochastic epidemic modelling), <https://doi.org/10.4161/viru.24041>, PMCID PMC3710332.
- H. Abbey, "An examination of the Reed–Frost theory of epidemics", Human Biology 24 (1952) 201–233.
