# Generalized transfer entropy with same-bin interactions and state conditioning

Let $x_i(t)$ be calcium fluorescence signals of nodes $i = 1, \dots, N$, sampled in time bins much longer than synaptic time constants. Preprocess by discrete differentiation, $y_i(t) = x_i(t) - x_i(t - 1)$, quantize $y_i$ into a small number of levels, and define the network-average signal

$$g_t = \frac{1}{N} \sum_{i=1}^{N} x_i(t).$$

For a conditioning threshold $\hat g$, restrict all probabilities to time points with $g_{n+1} < \hat g$ (a single dynamical regime, e.g. inter-burst periods). The **generalized transfer entropy** from $J$ to $I$ with Markov order $k$ is

$$\mathrm{TE}^{*}_{J \to I}(\hat g) = \sum P\big(i_{n+1}, i^{(k)}_n, j^{(k)}_{n+1} \,\big|\, g_{n+1} < \hat g\big) \log \frac{P\big(i_{n+1} \mid i^{(k)}_n, j^{(k)}_{n+1}, g_{n+1} < \hat g\big)}{P\big(i_{n+1} \mid i^{(k)}_n, g_{n+1} < \hat g\big)},$$

where $j^{(k)}_{n+1} = (j_{n+1}, j_n, \dots, j_{n-k+2})$ includes the present bin of the source.

Properties:

- it is a transfer entropy of the restricted joint process in which the source history is shifted by one bin, so it inherits non-negativity and vanishes exactly when, within the selected regime, $I_{n+1}$ is conditionally independent of $(J_{n+1}, \dots, J_{n-k+2})$ given $I^{(k)}_n$;
- including $j_{n+1}$ captures causal interactions faster than one acquisition bin ("same-bin" interactions), which the original definition cannot see because it uses only strictly past source values;
- restricting to $g_{n+1} < \hat g$ excludes synchronized network bursts, during which all nodes co-activate and pairwise statistics reflect the global state rather than direct connections.

## Depends on

- [Transfer entropy](transfer-entropy.md)

## Expansion

Both modifications change only which variables enter the conditional laws, so the information-theoretic properties of the original transfer entropy carry over to the restricted, shifted process. Network reconstruction scores every directed pair, ranks and rescales the scores to the unit interval, and keeps links above a threshold; on simulated networks of leaky integrate-and-fire neurons with realistic calcium and light-scattering artifacts, generalized transfer entropy with optimal conditioning outperformed cross-correlation, linear Granger causality and the original transfer entropy, and recovered clustering coefficients and connection length scales that linear methods systematically over- or underestimated.

## Sources

- O. Stetter, D. Battaglia, J. Soriano and T. Geisel, "Model-free reconstruction of excitatory neuronal connectivity from calcium imaging signals", PLoS Computational Biology 8 (2012), e1002653, Methods ("Generalized Transfer Entropy", "Network reconstruction"), Eqs. (10)–(11), <https://doi.org/10.1371/journal.pcbi.1002653> (PMC3426566).
