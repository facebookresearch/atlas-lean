# Wavelet Moran theorem and synchrony explained by drivers

**Setting.** Let $x^{(k)}_n(t)$, $k = 0, \dots, K$, be spatiotemporal variables at locations $n = 1, \dots, N$ and times $t = 1, \dots, T$, with $x^{(0)}$ a biological response and $x^{(k)}$, $k \ge 1$, candidate drivers. Let $w^{(k)}_{n,\sigma}(t)$ be their power-normalized complex wavelet transforms at timescale $\sigma$.

- The **wavelet mean field** is $r^{(k)}_\sigma(t) = \frac1N \sum_{n=1}^N w^{(k)}_{n,\sigma}(t)$; its magnitude measures time- and timescale-specific synchrony, and the **mean squared synchrony** is $\{|r^{(k)}_\sigma|\}_t = \frac1T \sum_t |r^{(k)}_\sigma(t)|^2$.
- A **wavelet linear model** is $w^{(0)}_{n,\sigma}(t) \approx \sum_{k=1}^K \beta_k(\sigma)\, w^{(k)}_{n,\sigma}(t)$ with complex coefficients $\beta_k(\sigma)$ (moduli are effect strengths, arguments are phase lags), fitted to maximize the spatial coherence between the two sides at each $\sigma$. Write $w^{(h)}_{n,\sigma} = \sum_k \beta_k(\sigma) w^{(k)}_{n,\sigma}$ for the fitted model transform and $\Pi^{(0h)}_\sigma$ for the spatial coherence of $x^{(0)}$ with the model ($0 \le |\Pi^{(0h)}_\sigma| \le 1$).

**Theorem (wavelet Moran theorem).** If, at timescale $\sigma$, the only synchronizing influences on $x^{(0)}$ are the drivers $x^{(1)}, \dots, x^{(K)}$ (all remaining variation being spatially independent), then

$$\{|r^{(0)}_\sigma|\}_t \approx \{|r^{(h)}_\sigma|\}_t\, \big|\Pi^{(0h)}_\sigma\big|^2 :$$

the synchrony of the response equals the synchrony of the best-fitting driver model times the squared coherence of that model with the response. Additional independent synchronizing drivers turn $\approx$ into $>$, so the right side is the synchrony attributable to the included drivers, and its ratio to the left side is the fraction of synchrony explained.

**Interaction decomposition.** Because the mean field is linear, $r^{(h)}_\sigma(t) = \sum_k \beta_k(\sigma)\, r^{(k)}_\sigma(t)$, hence

$$\{|r^{(h)}_\sigma|\}_t = \sum_{k} |\beta_k|^2 \{|r^{(k)}_\sigma|\}_t + \sum_{k \ne l} \frac1T \sum_t \mathrm{Re}\Big(\beta_k \overline{\beta_l}\, r^{(k)}_\sigma(t)\, \overline{r^{(l)}_\sigma(t)}\Big).$$

The first sum is the synchrony each driver would produce alone; the cross terms are interaction effects between Moran drivers. They are positive when the drivers' synchronous fluctuations, shifted by the phases of the $\beta_k$, arrive in phase at the response (reinforcement) and negative when they arrive out of phase (cancellation); destroying cross-driver phase relationships by surrogate randomization removes them.

## Depends on

- [Moran theorem for linear autoregressive populations](moran-theorem-for-linear-autoregressive-populations.md)

## Expansion

The theorem is a timescale-specific analogue of the classical Moran theorem: in the linear model the response transform is the driver combination plus local noise, the mean field averages the local noise away across locations, and the remaining synchronous part is the model mean field scaled by how strongly the model accounts for the response, which is what the coherence measures. In the analysed plankton data, long-timescale synchrony of a phytoplankton colour index was largely explained by a temperature (climatic) driver and a zooplankton grazer (top-down) driver whose phase relationships made their effects reinforce, so that interaction terms contributed substantially. A two-driver synthetic example shows the cross term changing sign as the phase offset between the drivers passes a quarter cycle.

## Sources

- L. W. Sheppard, E. J. Defriez, P. C. Reid and D. C. Reuman, "Synchrony is more than its top-down and climatic parts: interacting Moran effects on phytoplankton in British seas", PLoS Computational Biology 15 (2019), e1006744, Methods (Eq. 2; wavelet Moran theorem, theorem 1 of Appendix S14; synchrony attribution theorem, theorem 2 of Appendix S17) and Results (Fig. 1, Fig. 3), <https://doi.org/10.1371/journal.pcbi.1006744> (PMCID: PMC6438443).
