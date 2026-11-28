# Rescue probability in a gradually deteriorating environment

In the model of [mutant fixation under time-varying rates](fixation-probability-under-time-varying-birth-death-rates.md), wild-type organisms mutate to $M$ with probability $\mu$ per division, without back mutation, and the wild type alone goes extinct ($f_W(t) \to 0$ while $g_W > 0$). Let $p_{af}(t)$ be the probability that a mutant destined for fixation appears in $[0, t]$.

**Proposition.** Assume the population is essentially wild type when the rescuing mutant arises ($N_W \gg N_M$). Then $dp_{af} = (1 - p_{af})\, p_{\mathrm{fix}}(t)\, dN_M^{\mathrm{app}}(t)$ with $dN_M^{\mathrm{app}}(t) = \mu N_W(t) f_W(t)(1 - N_W(t)/K)\, dt$, hence $p_{af}(t) = 1 - e^{-\sigma(t)}$ with

$$\sigma(t) = \mu \int_0^t p_{\mathrm{fix}}(s)\, N_W(s)\, f_W(s)\Bigl(1 - \frac{N_W(s)}{K}\Bigr) ds,$$

and the **rescue probability** is

$$p_r = \lim_{t \to \infty} p_{af}(t) = 1 - e^{-\Sigma}, \qquad \Sigma = \mu \int_0^\infty p_{\mathrm{fix}}(t)\, N_W(t)\, f_W(t)\Bigl(1 - \frac{N_W(t)}{K}\Bigr) dt .$$

For $\Sigma \ll 1$, $p_r \approx \Sigma$. The appearance time $\hat\tau_{af}$ of the rescuing mutant, conditional on rescue, has density

$$F(t) = \frac{\mu}{p_r}\, p_{\mathrm{fix}}(t)\, N_W(t) f_W(t)\Bigl(1 - \frac{N_W(t)}{K}\Bigr) e^{-\sigma(t)},$$

and mean $\tau_{af} = \int_0^\infty t F(t)\, dt$.

## Depends on

- [Fixation probability of a mutant under time-varying birth and death rates](fixation-probability-under-time-varying-birth-death-rates.md)

## Expansion

Rescuing mutants form a thinned, time-inhomogeneous Poisson stream: mutants arise at rate $\mu N_W f_W(1 - N_W/K)$ and each is retained with probability $p_{\mathrm{fix}}$, so the first retained mutant arrives by time $t$ with probability $1 - e^{-\sigma(t)}$. The rescue probability rises sigmoidally in $K\mu$; a faster deterioration (larger Hill coefficient $n$) shifts the transition to larger $K\mu$ because fewer mutants arise before the wild type collapses. In the abrupt limit $n \to \infty$ rescue requires pre-existing mutants and the transition sits near $K\mu \approx 1$. The derivation stays accurate in the weak-to-moderate mutation regime $K\mu \lesssim 1$.

## Sources

- L. Marrec and A.-F. Bitbol, "Adapt or Perish: Evolutionary Rescue in a Gradually Deteriorating Environment", *Genetics* (2020), <https://doi.org/10.1534/genetics.120.303624> (PMC7536851; Equations (6)–(13)).
