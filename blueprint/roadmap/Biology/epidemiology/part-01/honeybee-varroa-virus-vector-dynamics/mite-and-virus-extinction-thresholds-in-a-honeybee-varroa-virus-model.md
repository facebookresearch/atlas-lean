# Mite and virus extinction thresholds in a honeybee–Varroa–virus model

**Model.** Let $S_h, I_h$ be healthy and virus-infected honeybees and $S_m, I_m$ virus-free and virus-carrying *Varroa* mites:

$$\begin{aligned} S_h' &= \frac{r(S_h + \rho I_h)^2}{\hat K + (S_h + \rho I_h)^2} - d_hS_h - \frac{\beta_hS_hI_h}{S_h + I_h} - \frac{\hat\beta_{mh}S_hI_m}{S_h + I_h} - \tilde\beta_{mh}S_hI_m - \alpha S_h(S_m + I_m),\\ I_h' &= S_h\Bigl[\frac{\beta_hI_h}{S_h + I_h} + \frac{\hat\beta_{mh}I_m}{S_h + I_h} + \tilde\beta_{mh}I_m\Bigr] - \alpha I_h(S_m + I_m) - (d_h + \mu_h)I_h,\\ S_m' &= S_m\Bigl[c\alpha S_h - \frac{\hat\beta_{hm}I_h}{S_h + I_h} - d_m\Bigr],\\ I_m' &= c\alpha\bigl[I_h(S_m + I_m) + S_hI_m\bigr] + \frac{\hat\beta_{hm}I_hS_m}{S_h + I_h} - (d_m + \mu_m)I_m . \end{aligned}$$

Brood production is sigmoidal in the number of bees, which gives a colony-level Allee effect, and infected bees contribute with relative fitness $\rho \in [0,1]$. Mites parasitize bees at rate $\alpha$ with conversion efficiency $c$. The virus spreads among bees (rate $\beta_h$), from mites to bees in the phoretic phase (frequency-dependent, $\hat\beta_{mh}$) and in the reproductive phase (density-dependent, $\tilde\beta_{mh}$), and from bees to mites ($\hat\beta_{hm}$). Let $d = \min\{d_h, d_m\}$ and define

$$N^* = c\,\frac{r/d + \sqrt{(r/d)^2 - 4\hat K}}{2}, \qquad \bar N_h^{c,*} = \frac{r/d_h \mp \sqrt{(r/d_h)^2 - 4\hat K}}{2}, \qquad \mathcal R_0^V = \frac{\beta_h}{d_h + \mu_h}.$$

**Theorem.**

1. (Boundedness.) If $r/d > 2\sqrt{\hat K}$, the nonnegative orthant is invariant and, for large times, $c(S_h + I_h) + (S_m + I_m) \le N^*$. If $r/(2\sqrt{\hat K}) < d_h$, the colony collapses: all populations go to $0$.
2. (Mite extinction.) If $N^* < d_m/\alpha$, the mites go extinct, and the dynamics reduce to the two-dimensional bee–virus system on the mite-free set.
3. (Bee persistence with healthy-mite extinction.) If $r/(2\sqrt{\hat K}) > d_h$, $\bar N_h^* < d_m/(\alpha c)$ and the initial number of healthy bees exceeds an explicit threshold, the bees persist while the virus-free mites go extinct.
4. (Colony survival.) If $r/(2\sqrt{\hat K}) > d_h$, $N^* < d_m/\alpha$ and $\mathcal R_0^V < 1$, the full system converges to the disease- and mite-free set, where $S_h' = rS_h^2/(\hat K + S_h^2) - d_hS_h$. The colony then tends to $\bar N_h^*$ if $S_h(0) > \bar N_h^c$ and collapses if $S_h(0) < \bar N_h^c$.

The virus-free bee–mite subsystem has one, three or four equilibria, and the mite-free bee–virus subsystem has one, three or five, with explicit existence and stability conditions. The origin (colony collapse) is always locally stable because of the Allee effect.

## Expansion

Adding $c$ times the bee equations to the mite equations cancels the parasitism terms. Since brood production is at most $r(S_h + \rho I_h)^2/(\hat K + (\cdot)^2)$, the weighted total $N = cN_h + N_m$ satisfies $N' \le c\,rN^2/(c^2\hat K + N^2) - dN$, whose largest equilibrium is $N^*$. Comparison then gives the bound. If $N^* < d_m/\alpha$, the per-capita mite growth $c\alpha S_h - d_m \le \alpha N^* - d_m$ is negative, which forces mite extinction. When moreover $\mathcal R_0^V < 1$, infected bees decay, and the bee equation reduces asymptotically to the scalar Allee equation, whose two positive equilibria $\bar N_h^c < \bar N_h^*$ solve $r N = d_h(\hat K + N^2)$.

## Sources

- Yun Kang, Krystal Blanco, Talia Davies, Ying Wang, "Disease dynamics of Honeybees with Varroa destructor as parasite and virus vector", arXiv (2015). Section 2 (rescaled model), Section 3: definitions of $N^*$ and $\bar N_h^{c,*}$, Theorems 3.1–3.6. <https://doi.org/10.48550/arXiv.1505.03742>. Published version: Mathematical Biosciences 275 (2016), 71–92, <https://doi.org/10.1016/j.mbs.2016.02.012>; locators above refer to the arXiv version.
