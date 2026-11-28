# Evolved correlation of growth rate and lag time

Consider adaptation in the [serial-dilution model](selection-coefficient-under-serial-dilution.md) in the strong-selection weak-mutation regime, where fixed mutations accumulate one at a time and each fixed mutation changes the relative growth rate by $\gamma$ and the relative lag by $\omega$. Write $\langle \cdot \rangle_{\mathrm{fixed}}$ for the average over the distribution of $(\gamma, \omega)$ among *fixed* single mutations, which is the mutational distribution $p_{\mathrm{mut}}(\gamma, \omega)$ reweighted by the [fixation probability](fixation-probability-under-serial-dilution.md) of $s = \gamma \ln D - \omega$.

**Same number of fixed mutations.** Across replicate populations that have accumulated the same number of fixed mutations, the Pearson correlation between the population growth rate and lag time is approximately

$$\rho_{\mathrm{fixed}} \approx \frac{\langle \gamma\omega \rangle_{\mathrm{fixed}} - \langle \gamma \rangle_{\mathrm{fixed}} \langle \omega \rangle_{\mathrm{fixed}}}{\sqrt{\bigl(\langle \gamma^2 \rangle_{\mathrm{fixed}} - \langle \gamma \rangle_{\mathrm{fixed}}^2\bigr)\bigl(\langle \omega^2 \rangle_{\mathrm{fixed}} - \langle \omega \rangle_{\mathrm{fixed}}^2\bigr)}},$$

the correlation of $(\gamma, \omega)$ within a single fixed mutation; it is positive for uncorrelated uniform or Gaussian mutational effects.

**Same elapsed time.** Across populations observed at the same time (same number of arising mutations, variable number of fixed ones), the correlation is approximately

$$\rho_{\mathrm{evo}} \approx \frac{\langle \gamma\omega \rangle_{\mathrm{fixed}}}{\sqrt{\langle \gamma^2 \rangle_{\mathrm{fixed}} \, \langle \omega^2 \rangle_{\mathrm{fixed}}}},$$

which is negative for every symmetric distribution $p_{\mathrm{mut}}$ with uncorrelated $\gamma$ and $\omega$.

The SSWM adaptation speeds per cycle are

$$W_{\mathrm{growth}} = \sigma_\gamma^2 r_0 \ln D \cdot \mu R Y_0 \frac{\ln D}{D-1}, \qquad W_{\mathrm{lag}} = -\frac{\sigma_\omega^2}{r_0} \cdot \mu R Y_0 \frac{\ln D}{D-1},$$

where $\sigma_\gamma, \sigma_\omega$ are the standard deviations of the mutational effects, $\mu$ the per-division mutation probability, and $r_0, Y_0$ the ancestral growth rate and yield, so that $W_{\mathrm{growth}}/W_{\mathrm{lag}} = -r_0^2 (\sigma_\gamma^2/\sigma_\omega^2) \ln D$ is independent of $R$ and $\mu$.

## Proof sketch

Selection keeps mutations with $\gamma \ln D - \omega > 0$, so among fixed mutations a large growth gain tolerates a lag increase and vice versa: the fixed distribution tilts toward positive covariance of $\gamma$ and $\omega$, giving $\rho_{\mathrm{fixed}} > 0$. At a fixed time, however, populations differ mainly in how many mutations they have fixed; each fixed mutation raises growth rate and shortens lag on average, so populations with more fixed mutations are both faster and quicker to exit lag, and the cross-population correlation turns negative (a Simpson's-paradox effect). The formula for $\rho_{\mathrm{evo}}$ follows by the law of total covariance with an approximately Poisson number of fixed mutations (a small fixation probability thinning a nearly fixed number of arising mutations), so that raw (uncentered) second moments of single fixed mutations govern the cross-population covariance. Observed trait correlations in evolved populations therefore mix mutational constraints with selection and cannot by themselves reveal a physiological trade-off.

## Depends on

- [Selection coefficient of growth traits under serial dilution](selection-coefficient-under-serial-dilution.md)
- [Fixation probability under serial dilution](fixation-probability-under-serial-dilution.md)

## Sources

- J. Lin, M. Manhart and A. Amir, "Evolution of microbial growth traits under serial dilution", Genetics (2020), <https://doi.org/10.1534/genetics.120.303149>, PMCID PMC7337084. Equations 8–11 and Figure 5.
