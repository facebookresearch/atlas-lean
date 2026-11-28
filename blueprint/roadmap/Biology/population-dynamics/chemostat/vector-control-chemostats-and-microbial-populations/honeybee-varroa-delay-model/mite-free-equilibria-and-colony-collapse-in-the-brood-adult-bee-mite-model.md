# Mite-free equilibria and colony collapse in the brood–adult bee–mite delay model

**Model.** Let $B(t)$, $H(t)$, $M(t)$ be the brood, adult honeybee and *Varroa* mite populations, with brood-to-adult development time $\tau > 0$ and positive parameters $r, K, a, \alpha_b, \alpha_h, c, d_b, d_h, d_m$. For $t > \tau$,

$$\frac{dB}{dt} = \frac{rH^2}{K + H^2} - \alpha_b \frac{B}{a+B} M - d_b B - S(t)\, \frac{r H(t-\tau)^2}{K + H(t-\tau)^2},$$

$$\frac{dH}{dt} = S(t)\, \frac{r H(t-\tau)^2}{K + H(t-\tau)^2} - \alpha_h \frac{H}{a+H} M - d_h H, \qquad \frac{dM}{dt} = c\,\alpha_b \frac{B}{a+B} M - d_m M,$$

where $S(t) = \exp\big(-\int_{t-\tau}^{t} [d_b + \alpha_b M(s)/(a + B(s))]\, ds\big)$ is the probability that an egg laid at $t - \tau$ survives natural death and parasitism to emerge as an adult. Egg production $rH^2/(K+H^2)$ is sigmoidal in the adult workforce. Mites reproduce only on brood.

**Theorem.** For nonnegative initial data with positive initial populations:

1. Solutions stay positive for $t > 0$ and $\limsup_{t \to \infty} (B + H + M) \le cr / \min\{d_b, d_h, d_m\}$.
2. The colony-extinction equilibrium $E_{000} = (0,0,0)$ always exists and is always locally asymptotically stable.
3. If $d_h < r e^{-d_b \tau} / (2\sqrt{K})$ there are two mite-free equilibria $E_i = (B_i^*, H_i^*, 0)$, $i = 1,2$, with

$$H_{1,2}^* = \frac{r e^{-d_b \tau}}{2 d_h}\left(1 \mp \sqrt{1 - \Big(\frac{2 d_h e^{d_b \tau}}{r}\Big)^2 K}\right), \qquad B_i^* = \frac{1 - e^{-d_b \tau}}{d_b}\, \frac{r (H_i^*)^2}{K + (H_i^*)^2}.$$

$E_1$ (smaller colony) is always unstable. $E_2$ is locally asymptotically stable if $d_m > c\alpha_b B_2^*/(a + B_2^*)$ and unstable if $d_m < c\alpha_b B_2^*/(a + B_2^*)$.
4. If $d_h > r e^{-d_b \tau}/(2\sqrt{K})$ and $d_m > c\alpha_b$, then $E_{000}$ is globally asymptotically stable: the colony collapses from every initial state.

## Expansion

On $M = 0$ the adult equation at equilibrium reads $e^{-d_b\tau} r H^2/(K + H^2) = d_h H$, i.e. $d_h H^2 - r e^{-d_b\tau} H + d_h K = 0$, which has two positive roots exactly when $r e^{-d_b \tau} > 2 d_h \sqrt{K}$. The sigmoidal recruitment makes the origin stable (a strong Allee effect) and the smaller root a saddle threshold. Mites invade the healthy colony $E_2$ exactly when their per-capita birth rate on its brood, $c\alpha_b B_2^*/(a + B_2^*)$, exceeds their death rate $d_m$. Since $e^{-d_b\tau}$ decreases in $\tau$, a long development delay can remove the mite-free equilibria altogether and drive the colony to collapse.

## Sources

- K. Messan, M. Rodriguez Messan, J. Chen and G. DeGrandi-Hoffman, "Population dynamics of Varroa mite and honeybee: Effects of parasitism with age structure and seasonality", arXiv:2003.12089 (2020), Section 2 (model), Section 3, Theorems 3.1, 3.2 and 3.3, <https://doi.org/10.48550/arXiv.2003.12089>.
