# Window boundaries and time in the mutant selection window

In the setting of the [mutant selection window](mutant-selection-window-and-wild-type-growth-window.md), assume an unchanged slope ($\sigma = 0$) and $R_{00}(1-s) > 1$. Then:

1. $\mathrm{WGW} = [0, D_{\mathrm{wt}})$ with $D_{\mathrm{wt}} = \mathrm{IC}_{50}\,(R_{00} - 1)^{1/m}$.
2. $\{D : R_0'(D) > 1\} = [0, D_{\mathrm{mut}})$ with $D_{\mathrm{mut}} = \rho\, \mathrm{IC}_{50}\,\big(R_{00}(1-s) - 1\big)^{1/m}$.
3. If $1 - s > \rho^{-m}$, then $R_0'(D) > R_0(D)$ iff $D > D_\times$, where

$$D_\times = \mathrm{IC}_{50} \left(\frac{s}{1 - s - \rho^{-m}}\right)^{1/m};$$

if $1 - s \le \rho^{-m}$ the mutant is never fitter and the MSW is empty.
4. Hence $\mathrm{MSW} = (D_\times, D_{\mathrm{mut}})$, nonempty iff $D_\times < D_{\mathrm{mut}}$.
5. With first-order elimination $D(t) = D_0\, 2^{-t/t_{1/2}}$ after a dose $D_0 \ge D_{\mathrm{mut}}$, the time spent in a nonempty MSW is

$$t_{\mathrm{MSW}} = t_{1/2} \log_2 \frac{D_{\mathrm{mut}}}{D_\times},$$

independent of the dose, while, for $D_0 \ge D_{\mathrm{wt}}$, the wild type starts to grow at $t_{\mathrm{WGW}} = t_{1/2}\log_2(D_0/D_{\mathrm{wt}})$.

## Depends on

- [Mutant selection window and wild-type growth window](mutant-selection-window-and-wild-type-growth-window.md)

## Expansion

Items 1–2 solve $R_0(D) = 1$ and $R_0'(D) = 1$, using that both curves decrease strictly in $D$. For item 3 put $u = (D/\mathrm{IC}_{50})^m$; then $R_0' > R_0$ iff $(1-s)(1+u) > 1 + \rho^{-m} u$, i.e. $u(1 - s - \rho^{-m}) > s$. Item 5 follows from $D(t) = D^*$ at $t = t_{1/2}\log_2(D_0/D^*)$, applied at $D_{\mathrm{mut}}$ and $D_\times$. The ratio $D_{\mathrm{mut}}/D_\times$ depends on the slope only through the power $1/m$, so steep dose–response curves compress the MSW in log-concentration and, for a given half-life, shorten the time in which resistance is selected; this is the mechanism behind the small time in the MSW for protease inhibitors reported by Rosenbloom et al., who compute these times numerically from measured pharmacokinetic and dose–response parameters (also with $\sigma \ne 0$). These closed forms are elementary consequences of the model's Equations 1–2, not formulas stated in the paper.

## Sources

- D. I. S. Rosenbloom, A. L. Hill, S. A. Rabi, R. F. Siliciano and M. A. Nowak, "Antiretroviral dynamics determines HIV evolution and predicts therapy outcome", Nature Medicine 18 (2012), Results ("Defining the mutant selection window", "The MSW explains therapy outcome patterns", Equations 1–2, Figures 1–2), <https://doi.org/10.1038/nm.2892>, PMCID: PMC3490032.
