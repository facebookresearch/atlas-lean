# Double-exponential sigmoid model of spike-to-fluorescence transformation

Given spike times $\{t_k\}$ of a neuron, the spike-to-fluorescence (S2F) forward model first forms a latent calcium-like variable

$$c(t) = \sum_{t_k < t} e^{-(t - t_k)/\tau_d}\bigl[1 - e^{-(t - t_k)/\tau_r}\bigr] + n_i(t), \qquad n_i(t) \sim N(0, \sigma_i^2),$$

with rise time $\tau_r > 0$, decay time $\tau_d > 0$ and internal noise $n_i$, truncating $c(t)$ at zero if noise drives it negative, and then a synthetic fluorescence trace

$$\frac{\Delta F}{F}_{\mathrm{synth}}(t) = \frac{F_m}{1 + \exp\bigl[-k\bigl(c(t) - c_{1/2}\bigr)\bigr]} + n_e(t), \qquad n_e(t) \sim N(0, \sigma_e^2),$$

with maximal fluorescence change $F_m$, sharpness $k$, half-activation $c_{1/2}$ and external noise $n_e$. The single-spike kernel $h(s) = e^{-s/\tau_d}(1 - e^{-s/\tau_r})$, $s \ge 0$, peaks at

$$s^\ast = \tau_r \log\Bigl(1 + \frac{\tau_d}{\tau_r}\Bigr),$$

and has Laplace transform $\hat h(\zeta) = \dfrac{1}{\zeta + 1/\tau_d} - \dfrac{1}{\zeta + 1/\tau_d + 1/\tau_r}$, a low-pass filter. The Hill alternative replaces the sigmoid by $f(c) = F_{\max} c^n / (c^n + K_d)$.

## Expansion

Setting $h'(s) = 0$ gives $e^{-s/\tau_r}(1/\tau_r + 1/\tau_d) = 1/\tau_d$, hence the peak time; for slow indicators $\tau_d \gg \tau_r$ and the peak delay grows like $\tau_r \log(\tau_d/\tau_r)$. The linear stage smooths and delays spike trains, and the static sigmoid then compresses high rates and suppresses isolated spikes below $c_{1/2}$. Fitted to simultaneous imaging and juxtacellular recordings, the model reproduced how imaging changes population analyses: trial-type selectivity of ramp-up neurons survived in synthetic fluorescence while many ramp-down neurons became non-selective, the first principal component shifted from temporal dynamics (about 99% of its variance in electrophysiology) towards trial-type selectivity, and the "peakiness" of activity across the trial was lower in imaging than in electrophysiology. Because the transformation is many-to-one and noisy, forward-modelling electrophysiology data into synthetic imaging is a more reliable way to compare the two modalities than spike inference from fluorescence.

## Sources

- Wei Z, Lin BJ, Chen TW, Daie K, Svoboda K, Druckmann S. A comparison of neuronal population dynamics measured with calcium imaging and electrophysiology. *PLoS Computational Biology* 16:e1008198 (2020), Methods, spike-to-fluorescence model, equations (1) and (2). DOI <https://doi.org/10.1371/journal.pcbi.1008198>. PMCID PMC7518847.
