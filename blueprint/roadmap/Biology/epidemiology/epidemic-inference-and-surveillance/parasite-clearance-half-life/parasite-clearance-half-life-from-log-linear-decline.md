# Parasite clearance half-life from log-linear decline

Let $P(t) > 0$ be the parasite density of a treated patient at time $t$ after the start of treatment, and suppose that after a lag phase ending at $t_{\mathrm{lag}} \ge 0$ the density declines log-linearly,

$$\log_e P(t) \;=\; c - k\,(t - t_{\mathrm{lag}}), \qquad t \ge t_{\mathrm{lag}},$$

with clearance rate constant $k > 0$. Then the parasite clearance half-life, the time for the density to halve during the log-linear phase, is

$$t_{1/2} \;=\; \frac{\log 2}{k},$$

independently of the starting density and of $t_{\mathrm{lag}}$. If the decline is fitted on the base-10 scale with slope $-s$ ($s > 0$), then $k = s \log 10$ and $t_{1/2} = \log_{10} 2 / s$. The time to clear a density $P_0$ to a detection limit $P_{\mathrm{d}} < P_0$ after the lag is $t_{1/2}\, \log_2(P_0/P_{\mathrm{d}})$, so clearance time depends on initial parasitaemia while the half-life does not. If $\log t_{1/2}$ is normally distributed in a population with mean $\mu$, the geometric mean half-life is $e^{\mu}$.

## Depends on

- [Half-life in terms of clearance and volume](../../../pharmacokinetics/one-compartment-linear-pharmacokinetics/half-life-elim-rate.md)

## Expansion

From the log-linear law, $P(t + t_{1/2})/P(t) = e^{-k t_{1/2}} = 1/2$ gives $t_{1/2} = \log 2/k$, the same relation as for first-order drug elimination. The base change uses $\log_e x = \log 10 \cdot \log_{10} x$. Clearing from $P_0$ to $P_{\mathrm{d}}$ takes $\log(P_0/P_{\mathrm d})/k$, which equals $t_{1/2}\log_2(P_0/P_{\mathrm d})$. The standardized fitting procedure first detects and removes the lag phase (during which counts level off or even rise) and the tail near the detection limit, then fits the log-linear segment; curves with poor log-linear fit are excluded. On the Thailand–Myanmar border, the geometric mean clearance half-life rose from about $2.6$ hours in 2001 to about $3.7$ hours in 2010, and the proportion of slow-clearing infections (half-life above $6.2$ hours) rose from $0.6\%$ to $20\%$, documenting the emergence of artemisinin resistance there.

## Sources

- A. P. Phyo, S. Nkhoma, K. Stepniewska, E. A. Ashley, S. Nair, R. McGready, et al., "Emergence of artemisinin-resistant malaria on the western border of Thailand: a longitudinal study", *The Lancet* 379(9830) (2012) 1960–1966, Methods, "Statistical analysis", <https://doi.org/10.1016/S0140-6736(12)60484-X> (PMC3525980).
