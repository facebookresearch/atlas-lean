# Mechanistic reproduction number and the SEIR generation interval

**Discrete-time stochastic SEIR model.** In a homogeneously mixing population of size $N$, with time-varying effective contact rate $\beta_t$ (mean number of contacts times transmission probability per susceptible–infectious contact), latent-period law $\pi^{\mathrm{EI}}$ on $\{1, 2, \dots\}$ and infectious-period law $\pi^{\mathrm{IR}}$ with mean $\mu^{\mathrm{IR}}$ and variance $(\sigma^{\mathrm{IR}})^2$,

$$E_t^* \sim \mathrm{Pois}\Big(\beta_t \frac{S_t I_t}{N}\Big), \qquad I_t^* \sim \mathrm{Pois}\Big(\sum_{s<t} E_s^* \pi^{\mathrm{EI}}_{t-s}\Big), \qquad R_t^* \sim \mathrm{Pois}\Big(\sum_{s<t} I_s^* \pi^{\mathrm{IR}}_{t-s}\Big),$$

with $S_{t+1} = S_t - E_t^*$, $E_{t+1} = E_t + E_t^* - I_t^*$, $I_{t+1} = I_t + I_t^* - R_t^*$. The **mechanistic reproduction number** is $R_t^M = \beta_t\, S_t\, \mu^{\mathrm{IR}} / N$. The **instantaneous reproduction number** is $R_t^I = \sum_{k > 0} w(t,k)$, where $w(t,k)$ is the expected number of transmissions at time $t$ per infection that occurred at time $t - k$. The **infectious kernel** is

$$\zeta_k^{\mathrm{EI}} = \mathbb{P}(\text{infectious } k \text{ days after infection}) = \sum_{j=1}^{k} \pi^{\mathrm{EI}}_j\, \mathbb{P}(W^{\mathrm{IR}} > k - j),$$

with latent and infectious durations $W^{\mathrm{EI}}$, $W^{\mathrm{IR}}$ independent.

**Proposition (equivalence).** Under homogeneous mixing, $R_t^I = R_t^M$. The proof rests on two identities: $\sum_{k \ge 1} \zeta_k^{\mathrm{EI}} = \mu^{\mathrm{IR}}$ for any delay laws, and $\mathbb{P}(i \text{ contacts } j \text{ at } t)\cdot \mathbb{P}(\text{transmission} \mid S\text{–}I \text{ contact}) = \beta_t / N$.

**Proposition (SEIR generation interval).** The SEIR model satisfies the renewal equation $\mathbb{E}[E_t^* \mid E_{<t}^*] = R_t^I \sum_{k \ge 1} E_{t-k}^*\, g_k$ with generation-interval weights

$$g_k = \frac{\zeta_k^{\mathrm{EI}}}{\mu^{\mathrm{IR}}} = \frac{\zeta_k^{\mathrm{EI}}}{\sum_j \zeta_j^{\mathrm{EI}}},$$

and mean generation time

$$\mathbb{E}[G] = \mu^{\mathrm{EI}} + \frac{\mu^{\mathrm{IR}}}{2} - \frac{1}{2} + \frac{(\sigma^{\mathrm{IR}})^2}{2\,\mu^{\mathrm{IR}}}.$$

## Expansion

For the kernel identity, swap the order of summation: $\sum_{k \ge 1}\zeta_k^{\mathrm{EI}} = \sum_{j \ge 1} \pi^{\mathrm{EI}}_j \sum_{a \ge 0} \mathbb{P}(W^{\mathrm{IR}} > a) = \mu^{\mathrm{IR}}$, because the tail sum of a nonnegative integer variable is its mean. For the contact identity, condition on the number $C_t$ of contacts: $\mathbb{P}(i \text{ contacts } j) = \mathbb{E}[C_t]/N$, and $\beta_t = \mathbb{E}[C_t]\,\mathbb{P}(\text{transmission} \mid \text{contact})$. Then $w(t,k) = S_t\, \zeta_k^{\mathrm{EI}}\, \beta_t / N$, and summing over $k$ gives $R_t^M$. For the generation interval, write prevalence as $I_t = \sum_{k \ge 1} E_{t-k}^* \zeta_k^{\mathrm{EI}}$ and substitute into $\mathbb{E}[E_t^* \mid I_t] = \beta_t S_t I_t / N = R_t^I I_t / \mu^{\mathrm{IR}}$; the tower rule handles the stochastic case. The mean follows from $\sum_k k\,\zeta_k^{\mathrm{EI}} / \mu^{\mathrm{IR}} = \mu^{\mathrm{EI}} + \mathbb{E}[W^{\mathrm{IR}}(W^{\mathrm{IR}} - 1)]/(2\mu^{\mathrm{IR}})$. The practical point is that any generation interval chosen for a renewal-equation estimator implicitly fixes the first two moments of a latent and an infectious period.

## Sources

- Jeremy Goldwasser, "Estimating Epidemic Rate Parameters: Adaptivity, Bias, and Convolution", arXiv (2026). Chapter "Unifying Perspectives on $R_t$": section "Equivalence of Instantaneous and Mechanistic $R_t$" (equivalence proposition and its two lemmas) and section "The SEIR Generation Interval" (generation-interval proposition). <https://doi.org/10.48550/arXiv.2608.10138>
