# Generation interval distribution implied by SEIR dynamics

In the discrete-time SEIR model with time-varying contact rate $\beta_t$, latent period $W^{EI}$ with distribution $\pi^{EI}$ and mean $\mu^{EI}$, and infectious period $W^{IR}$ with distribution $\pi^{IR}$, mean $\mu^{IR}$ and variance $(\sigma^{IR})^2$, define the infectious kernel

$$ \zeta^{EI}_k = \Pr(\text{infectious } k \text{ days after infection}) = \sum_{j=1}^{k} \Pr(W^{EI} = j)\, \Pr(W^{IR} > k - j), \qquad k \ge 1. $$

**Proposition 2.** Under homogeneous mixing, the generation interval distribution that makes the SEIR incidence satisfy the renewal equation $\mathbb{E}[x_t \mid x_{<t}] = R_t \sum_{k>0} x_{t-k}\, g_k$ has weights

$$ g_k = \Pr(\text{transmission } k \text{ days after exposure} \mid \text{transmission occurs}) = \frac{\zeta^{EI}_k}{\mu^{IR}} = \frac{\zeta^{EI}_k}{\sum_j \zeta^{EI}_j}, $$

and the mean generation time is

$$ \mathbb{E}[G] = \mu^{EI} + \frac{\mu^{IR}}{2} - \frac{1}{2} + \frac{(\sigma^{IR})^2}{2\, \mu^{IR}}. $$

So the generation interval is the convolution of the latent period with the length-biased residual infectious time, and it depends on the variance of the infectious period, not only on its mean. In an SIR model the kernel reduces to the survival function of $W^{IR}$. Consequently, a generation interval fed into a renewal-equation estimator of $R_t$ is not assumption-free: it encodes a specific compartmental structure and choice of delay distributions.

## Depends on

- [Equivalence of instantaneous and mechanistic reproduction numbers](equivalence-of-instantaneous-and-mechanistic-reproduction-numbers.md)

## Expansion

Under homogeneous mixing the transmission rate of an infection of age $k$ is $w(t,k) = \zeta^{EI}_k\, \beta_t S_t / N$, so its normalization $g_k = w(t,k) / \sum_j w(t,j)$ does not depend on $t$ and equals $\zeta^{EI}_k / \sum_j \zeta^{EI}_j$, with $\sum_j \zeta^{EI}_j = \mu^{IR}$. For the mean, $G = W^{EI} + U$, where given $W^{EI}$ the time $U$ since becoming infectious has distribution proportional to $\Pr(W^{IR} > u)$, $u \ge 0$; the discrete identity $\sum_{u \ge 0} u \Pr(W^{IR} > u) = \mathbb{E}[W^{IR}(W^{IR} - 1)]/2$ gives $\mathbb{E}[U] = \frac{(\sigma^{IR})^2 + (\mu^{IR})^2 - \mu^{IR}}{2 \mu^{IR}}$, and adding $\mu^{EI}$ yields the formula.

## Sources

- Jeremy Goldwasser, Ryan J. Tibshirani, Alyssa Bilinski, "On the Equivalence of Instantaneous and Mechanistic Reproduction Numbers", arXiv (2026). Section 4 (Proposition 2) and the appendix proof of the mean generation time. <https://doi.org/10.48550/arXiv.2606.15397>
