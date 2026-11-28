# Household reproduction number from the growth rate

**Setting.** In the household model with Reed–Frost within-household chains and size-biased household sizes, let $\mu_i$ be the expected number of cases in generation $i$ of a typical infected household ($\mu_1 = 1$, $\mu = \sum_i \mu_i$). Each infected individual infects on average $R_G$ people outside its household, with between-household infectiousness $\beta_G(\tau) = R_G\, w(\tau)$, and within-household generation gaps are also drawn from the generation-time density $w$ (with $\int_0^\infty w = 1$). Let $w^{[i]}$ denote the $i$-fold convolution power of $w$ ($w^{[0]} = \delta_0$). The household reproduction number $R_*$ is the mean number of households infected by one infected household.

**Proposition.**

1. $R_* = \mu\, R_G$.
2. The household generation-time density is $w_*(\tau_*) = \frac{1}{\mu}\sum_i \mu_i\, w^{[i]}(\tau_*)$, with mean $T_g^* = T_g \sum_i i\, \mu_i / \mu$, where $T_g$ is the mean of $w$.
3. If incidence grows exponentially at rate $r$ and $R(r) = 1/\int_0^\infty e^{-r\tau} w(\tau)\, d\tau$ is the individual reproduction number computed ignoring households, then

$$R_*(r) = \frac{\mu}{\sum_i \mu_i\, R(r)^{-i}}, \qquad R_G(r) = \frac{1}{\sum_i \mu_i\, R(r)^{-i}} .$$

Without within-household transmission ($\mu_1 = \mu = 1$) these reduce to $R_* = R_G = R(r)$.

## Depends on

- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)
- [Reed–Frost chain probabilities in size-biased households](reed-frost-chain-probabilities-in-size-biased-households.md)
- [Case reproduction number as a smoothed instantaneous reproduction number](../../epidemic-inference-and-surveillance/case-and-instantaneous-reproduction-numbers/case-reproduction-number-as-a-smoothed-instantaneous-reproduction-number.md)

## Proof depends on

- [Euler–Lotka equation for the reproductive number](../../euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff-reproduction-number.md)

## Expansion

A generation-$i$ case is infected at a time distributed as $w^{[i-1]}$ after the household's index case, and then infects outside the household with profile $R_G w$, so its contribution to the household's outward infectiousness is $R_G (w^{[i-1]} * w) = R_G w^{[i]}$. Summing over the household gives the household infectiousness $R_G \sum_i \mu_i w^{[i]}$, whose total mass is $R_G \mu$ (item 1) and whose normalized shape is $w_*$ (item 2). The exponential growth rate is the same for individual and household incidence, so the Euler–Lotka relation applied at the household level gives $R_* = 1/\int e^{-r\tau} w_*(\tau)\, d\tau$. The Laplace transform of a convolution is the product of transforms, so $\int e^{-r\tau} w^{[i]} = R(r)^{-i}$, which yields item 3. Ignoring saturation of within-household generation times overestimates $R_*$; putting all secondary household cases in generation 2 ($\mu_2' = \sum_{i \ge 2}\mu_i$) gives a practical lower bound.

## Sources

- C. Fraser, *Estimating individual and household reproduction numbers in an emerging epidemic*, PLoS ONE (2007). <https://doi.org/10.1371/journal.pone.0000758> (PMCID: PMC1950082). Methods, Equations (1)–(12) and (22)–(39).
