# Synchronization period in a GnRH neuron network model

**Model.** For neurons $j = 1,\dots,N$ with electrical variables $(x_j, y_j)$ of FitzHugh–Nagumo type and intracellular calcium $\mathrm{Ca}_j$, and one network-level synchronization variable $\sigma$,

$$x_j' = \tau\bigl(-y_j + 4x_j - x_j^3 - \phi_{\mathrm{fall}}(\mathrm{Ca}_j)\bigr),\qquad y_j' = \tau\varepsilon k_j\bigl(x_j + a_1 y_j + a_2 - \eta_j\,\phi_{\mathrm{syn}}(\sigma)\bigr),$$

$$\mathrm{Ca}_j' = \tau\varepsilon\Bigl(\phi_{\mathrm{rise}}(x_j) - \frac{\mathrm{Ca}_j - \mathrm{Ca}_{\mathrm{bas}}}{\tau_{\mathrm{Ca}}}\Bigr),\qquad \sigma' = \tau\Bigl(\delta\varepsilon\,\sigma - \gamma(\sigma - \sigma_0)\,\phi_\sigma\Bigl(\frac1N\sum_{i=1}^N \mathrm{Ca}_i - \mathrm{Ca}_{\mathrm{desyn}}\Bigr)\Bigr),$$

with $0 < \varepsilon \ll 1$, sigmoids $\phi_{\mathrm{syn}}(\sigma) = \bigl(1 + e^{-\rho_{\mathrm{syn}}(\sigma - \sigma_{\mathrm{on}})}\bigr)^{-1}$ and $\phi_\sigma$ of steepness $\rho_\sigma$, and $0 < \sigma_0 < \sigma_{\mathrm{on}}$. When $\sigma$ exceeds $\sigma_{\mathrm{on}}$, the input $\eta_j\phi_{\mathrm{syn}}(\sigma)$ pushes all neurons into a common firing regime (synchronized calcium peak); high mean calcium then activates $\phi_\sigma$ and resets $\sigma$ towards $\sigma_0$.

1. **Scaling invariance.** For every $\alpha > 0$, the calcium outputs $\mathrm{Ca}_j$ are unchanged when $(\sigma_0, \sigma_{\mathrm{on}}, \rho_{\mathrm{syn}})$ is replaced by $(\alpha\sigma_0, \alpha\sigma_{\mathrm{on}}, \rho_{\mathrm{syn}}/\alpha)$; only the ratio $\sigma_{\mathrm{on}}/\sigma_0$ matters.
2. **Synchronization period.** In the limit $\rho_\sigma = \infty$ (switch-like reset) and for $\gamma$ large relative to $\varepsilon$ and $\delta$, the time between two successive synchronization episodes is approximately

$$T_{\mathrm{syn}} = \frac{1}{\tau\varepsilon\delta}\,\ln\frac{\sigma_{\mathrm{on}}}{\sigma_0}.$$

Consequently any prescribed period $T_{\mathrm{syn}} > 0$ is obtained by choosing $\delta = \ln(\sigma_{\mathrm{on}}/\sigma_0)/(\tau\varepsilon T_{\mathrm{syn}})$, with all other parameters fixed.

## Expansion

Item 1 follows by substituting $\sigma \mapsto \alpha\sigma$: the $\sigma$-equation is linear-affine in $(\sigma, \sigma_0)$ and $\phi_{\mathrm{syn}}$ depends on $\rho_{\mathrm{syn}}(\sigma - \sigma_{\mathrm{on}})$, so the rescaled system is identical in the original variables. For item 2, during a synchronization episode the reset term dominates ($\gamma \gg \varepsilon\delta$) and drives $\sigma$ quickly to the quasi-equilibrium $\bar\sigma = \gamma\sigma_0/(\gamma - \delta\varepsilon) = \sigma_0 + O(\varepsilon\delta/\gamma)$. Once mean calcium falls below $\mathrm{Ca}_{\mathrm{desyn}}$, the switch $\phi_\sigma$ is off and $\sigma' = \tau\delta\varepsilon\,\sigma$, so $\sigma(t) = \sigma_0 e^{\tau\varepsilon\delta t}$ reaches $\sigma_{\mathrm{on}}$ after time $\ln(\sigma_{\mathrm{on}}/\sigma_0)/(\tau\varepsilon\delta)$, when the next episode starts. The hour-scale pulse period is therefore set by a single slow growth rate rather than by the faster individual calcium oscillations, which remain asynchronous between episodes.

## Sources

- M. Krupa, A. Vidal, F. Clément, "A network model of the periodic synchronization process in the dynamics of calcium concentration in GnRH neurons", *Journal of Mathematical Neuroscience* (2013), network model section (system (6a)–(6d), Proposition 1 with Eqs. (10)–(12), Proposition 2 with Eq. (13), Remark 2), <https://doi.org/10.1186/2190-8567-3-4> (PMC3652785).
