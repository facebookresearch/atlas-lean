# Equivalence of instantaneous and mechanistic reproduction numbers

**Instantaneous $R_t$.** Let $x_t$ be the number of infections at (discrete) time $t$ and $w(t,k) = \mathbb{E}[\#\text{transmissions at } t \mid \text{individual infected at } t-k]$ the rate of transmission at time $t$ of a primary infection of age $k$, so that $\mathbb{E}[x_t \mid x_{<t}] = \sum_{k>0} x_{t-k}\, w(t,k)$. The instantaneous reproduction number and the generation interval distribution are

$$ R_t^I = \sum_{k>0} w(t,k), \qquad g_k = \frac{w(t,k)}{R_t^I}, $$

which gives the renewal equation $\mathbb{E}[x_t \mid x_{<t}] = R_t^I \sum_{k>0} x_{t-k}\, g_k$.

**Mechanistic $R_t$.** Consider the discrete-time stochastic SEIR model on a population of size $N$ with time-varying effective contact rate $\beta_t$ and arbitrary exposed-to-infectious and infectious-to-recovered delay distributions $\pi^{EI}$, $\pi^{IR}$ (mean $\mu^{IR}$):

$$ S_{t+1} = S_t - E_t^*, \quad E_t^* \sim \mathrm{Pois}\Bigl( \beta_t \frac{S_t I_t}{N} \Bigr), \qquad I_t^* \sim \mathrm{Pois}\Bigl( \sum_{s<t} E_s^* \pi^{EI}_{t-s} \Bigr), \qquad R_t^* \sim \mathrm{Pois}\Bigl( \sum_{s<t} I_s^* \pi^{IR}_{t-s} \Bigr), $$

with $E, I, R$ updated by the corresponding inflows and outflows. The mechanistic reproduction number is

$$ R_t^M = \beta_t \frac{S_t\, \mu^{IR}}{N}, $$

reducing to $\beta S_t / (\gamma N)$ for exponential infectious periods.

**Proposition 1.** Under homogeneous mixing (every pair of individuals equally likely to make contact), $R_t^I = R_t^M$.

The proof rests on two lemmas. (Lemma 1) For any delay distributions, $\sum_{k>0} \Pr(\text{infectious } k \text{ days after infection}) = \mu^{IR}$. (Lemma 2) Under homogeneous mixing, $\Pr(i \text{ contacts } j \text{ at } t) \cdot \Pr(\text{transmission} \mid S\text{-}I \text{ contact}) = \beta_t / N$.

## Expansion

An individual infected $k$ days ago transmits at time $t$ only if it is infectious then, and while infectious it infects each of the $S_t$ susceptibles with probability $\beta_t / N$ (Lemma 2). Hence $w(t,k) = \zeta_k\, \beta_t S_t / N$, where $\zeta_k = \Pr(\text{infectious } k \text{ days after infection})$. Summing over $k$ and using Lemma 1, $\sum_k \zeta_k = \mu^{IR}$, gives $R_t^I = \beta_t S_t \mu^{IR} / N = R_t^M$. Lemma 1 follows by writing $\zeta_k = \sum_{j=1}^{k} \Pr(W^{EI} = j) \Pr(W^{IR} > k - j)$, exchanging the sums, and using that the survival function of a non-negative integer variable sums to its mean. So the renewal-equation and compartmental definitions agree, and the difference between $R_t$ estimates from the two frameworks comes from the assumed generation interval rather than from the definition.

## Sources

- Jeremy Goldwasser, Ryan J. Tibshirani, Alyssa Bilinski, "On the Equivalence of Instantaneous and Mechanistic Reproduction Numbers", arXiv (2026). Section 2, Section 3 (Proposition 1, Lemmas 1 and 2). <https://doi.org/10.48550/arXiv.2606.15397>
