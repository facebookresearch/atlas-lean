# Allelic and demographic persistence in the SAS-CFF model

**Model.** A diploid, randomly mating population with discrete generations has $k$ alleles at one locus with frequencies $X(t) \in \Delta$ (the probability simplex) and density $N(t)$. Allele $i$ contributes $Y_i(t)$ additively to a physiological activity, and genotype $A_iA_j$ has low-density fitness $\phi\big((Y_i + Y_j)/2\big)$ for a $C^3$ function $\phi$. With $W_i = \sum_j X_j\,\phi\big((Y_i + Y_j)/2\big)$, $W = \sum_i X_i W_i$ and a density-dependent factor $f$ with $f(0) = 1$, $f(N) \to 0$ as $N \to \infty$,

$$N(t+1) = N(t)\, W(X(t), Y(t))\, f(N(t)), \qquad X_i(t+1) = X_i(t)\,\frac{W_i(X(t), Y(t))}{W(X(t), Y(t))}.$$

Small symmetric fluctuations: $Y_i(t) = 1 + \varepsilon^2\mu + \varepsilon\sigma Z_i(t)$ with $(Z(t))_t$ i.i.d. in time, $\mathbb{E} Z_i = 0$, $\operatorname{Var} Z_i = 1$, $\operatorname{Corr}(Z_i, Z_j) = \rho \in [-1/(k-1), 1)$. Normalize $\phi(1) = \phi'(1) = 1$ and let $\gamma = (\log\phi)''(1) = \phi''(1) - 1$; $\gamma < 0$ for concave or mildly convex fitness. Let $\Delta_0$ be the set where some allele is absent and $S_0 = \Delta \times \{0\}$ the set where $N = 0$.

**Theorem.** Let $\varepsilon > 0$ be sufficiently small.

*(1)* *(Invasion rate of a rare allele.)* If the resident dynamics support $\ell < k$ alleles, a missing allele has realized per-capita growth rate $r_i = -\varepsilon^2\frac{\sigma^2(1 - \rho)\gamma}{4\ell} + O(\varepsilon^3)$.

*(2)* *(Allelic diversity.)* If $\gamma < 0$, the allele frequencies are $\Delta_0$-stochastically persistent (all $k$ alleles are maintained). If $\gamma > 0$, one allele fixes with probability one, and each allele present initially fixes with positive probability.

*(3)* *(Persistence under fixation.)* If $\gamma > 0$, the population persists ($S_0$-stochastically persistent) when $\mu + \sigma^2\gamma/2 > 0$ and $N(t) \to 0$ almost surely when $\mu + \sigma^2\gamma/2 < 0$.

*(4)* *(Persistence under polymorphism.)* If $\gamma < 0$, the population's growth rate at low density on the polymorphic ergodic state is

$$r_N = \varepsilon^2\Big(\mu + \frac{\sigma^2\gamma}{2} + \frac{\sigma^2\gamma(\gamma - 1)(1 - \rho)}{2(1 - 2\gamma)}\Big(1 - \frac1k\Big)\Big) + O(\varepsilon^3);$$

if $r_N > 0$ the population and all alleles persist ($S_0$- and $\Delta_0$-stochastically persistent, as in Theorem 3.3), and if $r_N < 0$ then $N(t) \to 0$ almost surely.

The last term is positive when $\gamma < 0$ and grows with the number of alleles $k$ and with $1 - \rho$: the same environmental fluctuations that maintain genetic diversity also raise the population growth rate, so allelic diversity can be necessary for persistence.

## Depends on

- [Directional selection, overdominance and underdominance at one locus](../../one-locus-selection-dynamics/one-locus-viability-selection-regimes.md)

## Expansion

Stochastic persistence follows from positivity of the invasion growth rates $r = \lim_t t^{-1}\log(\cdot)$ of rare alleles and of the population at low density, computed on ergodic stationary resident states (the law of large numbers for ergodic sequences). A second-order Taylor expansion of $\log(W_i/W)$ in $\varepsilon$ around $Y \equiv 1$ gives the rate of a missing allele: its mean is proportional to $-\gamma(1 - \rho)\sigma^2$, the variance of the allelic contrasts, so concave log-fitness rewards rarity. The population rate $r_N = \mathbb{E}\log W$ on the resident state gains from the reduced variance of mean fitness when $k$ alleles average independent fluctuations, a portfolio effect that offsets the classical variance penalty $\sigma^2\gamma/2$.

## Sources

- Sebastian J. Schreiber, *When do factors promoting genetic diversity also promote population persistence? A demographic perspective on Gillespie's SAS-CFF model*, Theor. Popul. Biol. 133 (2020), 141–149. <https://doi.org/10.1016/j.tpb.2019.07.013> Section 2 (model and stochastic persistence), Lemmas 3.1–3.3, Theorems 3.1–3.3. Locators use the numbering of the preprint, titled *When do factors promoting balanced selection also promote population persistence? A demographic perspective on Gillespie's SAS-CFF model*, arXiv:1902.03507.
