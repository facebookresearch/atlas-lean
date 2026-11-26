# Independent gamma rates relaxed clock

Let a clock tree have branch durations $\Delta_e > 0$ in time units and a base clock rate $c > 0$, so that branch $e$ has expected length $\ell_e = c\,\Delta_e$ in substitutions per site. Under the independent gamma rates (IGR) relaxed clock with variance-increase parameter $\sigma^2 > 0$, the effective length $B_e$ of branch $e$ (the length that enters the substitution likelihood) is drawn independently across branches as

$$B_e \;\sim\; \mathrm{Gamma}\bigl(\text{shape } \ell_e/\sigma^2,\ \text{scale } \sigma^2\bigr), \qquad \mathbb{E} B_e = \ell_e, \quad \operatorname{Var} B_e = \sigma^2 \ell_e .$$

Equivalently, the average rate on the branch is $c\,B_e/\ell_e$. The model has no time structure: if a branch of expected length $\ell$ is subdivided at an unsampled point into pieces of expected lengths $\ell_1 + \ell_2 = \ell$ with independent IGR effective lengths $B_1$ and $B_2$, then $B_1 + B_2$ has exactly the law $\mathrm{Gamma}(\ell/\sigma^2, \sigma^2)$ of the undivided branch. Hence the law of the total effective length along any path depends only on its total expected length, not on how the path is broken into branches.

## Expansion

The mean and variance follow from those of the gamma law (shape times scale, shape times scale squared). The subdivision property is closure of the gamma family under convolution with a common scale: independent $\mathrm{Gamma}(k_1, \theta)$ and $\mathrm{Gamma}(k_2, \theta)$ variables sum to $\mathrm{Gamma}(k_1 + k_2, \theta)$, as seen from the Laplace transforms $(1 + \theta s)^{-k}$. Thus the IGR effective lengths form the increments of a gamma subordinator in units of expected substitutions, which is why the model is uncorrelated across branches yet consistent under refinement of the tree. Uncorrelated lognormal or gamma models with a fixed rate variance per branch lack this property. Autocorrelated alternatives include the Thorne–Kishino lognormal model and the compound Poisson process. Because the variance of effective lengths grows linearly in time, $\sigma^2$ can be centred empirically on the slope of the squared deviations of non-clock branch lengths from their clock expectations against branch duration.

## Sources

- F. Ronquist, S. Klopfstein, L. Vilhelmsen, S. Schulmeister, D. L. Murray, A. P. Rasnitsyn, "A total-evidence approach to dating with fossils, applied to the early radiation of the Hymenoptera", *Systematic Biology* 61(6) (2012) 973–999, Materials and Methods, "Outline of Analyses" (description of the TK02, CPP and IGR relaxed-clock models) and "Relaxed-Clock Prior Parameters" (Figure 2), <https://doi.org/10.1093/sysbio/sys058> (PMC3478566).
