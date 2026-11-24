# Information-theoretic lower bounds for demographic inference

Terhorst and Song (2015) show that even when a population-size history is identifiable from the expected site-frequency spectrum, its estimation from $s$ independent segregating sites is slow: the minimax error of estimating the size history from the spectrum is at least of order $1/\log s$, for populations that have experienced a bottleneck, and the bound does not depend on the number of sampled individuals. Their Theorem 1 bounds the Kullback–Leibler divergence between the normalized expected spectra of two histories $\eta, \eta'$ that agree up to a time $t_c$ and satisfy $\max_{t > t_c}\eta(t) \le \min_{t > t_c}\eta'(t)$; their Theorem 3 gives an exponentially small bound for a family of piecewise-constant histories with a bottleneck, independent of $n$; and the histories are normalized by $\eta(0) = N_{\mathrm{fix}}$, since $\eta$ and $\kappa\eta(\cdot/\kappa)$ give the same normalized spectrum. The target is the precise family of histories, the observation model and loss, the divergence bounds and the minimax lower bound.

## Expansion

1. The observation model: independent segregating sites with frequencies drawn from the normalized expected spectrum.
2. The bottleneck family and the KL divergence between the induced spectra, as a function of the bottleneck time.
3. Le Cam's two-point method and the minimax lower bound of order $1/\log s$ under the stated loss.
4. The dependence on sample size and the limitations of the bound.

## Sources

- J. Terhorst and Y. S. Song, Fundamental limits on the accuracy of demographic inference based on the sample frequency spectrum, Proc. Natl. Acad. Sci. USA 112 (2015), 7677–7682. <https://doi.org/10.1073/pnas.1503717112>
