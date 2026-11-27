# Geometric law of reinfection counts at the SEIRS endemic equilibrium

Consider the SEIRS model with birth rate $b \ge 0$, natural death rate $\mu \ge 0$, contact rate $\beta > 0$, latency exit rate $\sigma > 0$, recovery rate $\gamma > 0$, waning rate $\omega > 0$ and disease-induced death rate $\nu \ge 0$. Split every compartment by the number of infections an individual has had: for $i \ge 1$, $S_i$ are susceptibles who have recovered $i-1$ times, $E_i$ and $I_i$ are exposed and infectious individuals in their $i$-th infection, and $R_i$ are those immune after their $i$-th recovery. The reinfection-counting system is

$$ \dot S_i = \omega R_{i-1} - \beta S_i \tfrac{I}{N} - \mu S_i, \quad \dot E_i = \beta S_i \tfrac{I}{N} - (\sigma+\mu) E_i, \quad \dot I_i = \sigma E_i - (\gamma+\mu+\nu) I_i, \quad \dot R_i = \gamma I_i - (\omega+\mu) R_i, $$

with $I = \sum_i I_i$, $N = \sum_i (S_i + E_i + I_i + R_i)$ and the convention $\omega R_0 = bN$ (newborns enter $S_1$). Summing over $i$ recovers the classical SEIRS system.

**Well-posedness.** For every nonnegative initial condition in $(\ell^1)^4$ with $\sum_i (E_i(0) + I_i(0)) > 0$ and every $T > 0$, there is a unique solution on $[0, T)$; it is positive for $t > 0$ and its totals solve the SEIRS system.

**Threshold and endemic profile.** Let $\bar S_i = S_i / N$ etc. be the fractions and

$$ \mathcal R_0 = \frac{\sigma}{\sigma+b} \cdot \frac{\beta}{\gamma+\nu+b}. $$

- If $\mathcal R_0 < 1$, every fraction tends to $0$ except $\bar S_1 \to 1$.
- If $\mathcal R_0 > 1$, the aggregated normalized system has a unique positive equilibrium $(\bar S^*, \bar E^*, \bar I^*, \bar R^*)$, and with

$$ \phi = \frac{\omega}{(\beta-\nu)\bar I^* + b} \cdot \frac{\gamma}{\omega + b - \nu \bar I^*} \cdot \frac{\bar I^*}{\bar S^*} \in (0,1), $$

every indexed fraction converges geometrically in the index: $(\bar S_i, \bar E_i, \bar I_i, \bar R_i) \to \phi^{i-1} (\bar S_1^*, \bar E_1^*, \bar I_1^*, \bar R_1^*)$ for each $i \ge 1$, with $\bar S_1^* = b / ((\beta-\nu)\bar I^* + b)$ and $\bar I_1^* = \bar S_1^* \bar I^* / \bar S^*$.

**Mean numbers of reinfections.** If $\mathcal R_0 > 1$, at the endemic equilibrium the number of past infections of a susceptible has mean $\phi/(1-\phi)$, and the infection rank of an exposed, infectious or recovered individual has mean $1/(1-\phi)$. Without disease mortality ($\nu = 0$) everything is explicit:

$$ \phi = \frac{\gamma\omega(\mathcal R_0 - 1)}{\beta(\omega+b) - \gamma\omega}, \qquad \bar I^* = \frac{\mathcal R_0 - 1}{\mathcal R_0} \cdot \frac{\sigma b (\omega + b)}{(\gamma+b)(\sigma+b)(\omega+b) - \omega\gamma\sigma}, $$

so the mean rank $1/(1-\phi) = (\beta(\omega+b) - \gamma\omega)/(\beta(\omega+b) - \gamma\omega\mathcal R_0)$.

## Expansion

Existence follows by truncating the infinite system and passing to the limit, using that the totals obey the finite SEIRS system; uniqueness comes from a Grönwall estimate in $\ell^1$. Normalizing by $N$ removes $\mu$. At the endemic equilibrium the indexed equations are linear with the known force of infection $\beta \bar I^*$, so they form a first-order recursion in $i$: each recovered class $\bar R_{i-1}$ feeds $\bar S_i$ with the same gain at every step, and that gain is $\phi$. A geometric profile in $i$ means that the number of past infections is geometrically distributed, and the means follow from $\sum_i i \phi^{i-1} = (1-\phi)^{-2}$. The paper (Theorems 1, 2 and 4, Corollaries 1 and 2) also describes the growth or decay of $N$ according to the signs of $b - \mu$ and $b - \mu - \nu \bar I^*$ (Theorem 3).

## Sources

- M. Fang and P.-A. Bliman, *Modelling, Analysis, Observability and Identifiability of Epidemic Dynamics with Reinfections*, arXiv:2201.10157 (2022), Theorems 1–4, Corollaries 1–2. <https://doi.org/10.48550/arXiv.2201.10157> Published version: 2022 European Control Conference (ECC) (2022) 278–283, <https://doi.org/10.23919/ecc55457.2022.9838334>.
