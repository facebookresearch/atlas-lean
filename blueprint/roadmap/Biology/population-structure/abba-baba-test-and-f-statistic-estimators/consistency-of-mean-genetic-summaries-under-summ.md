# Averages with summable autocovariances converge in mean square

Let $(Z_i)_{i \ge 0}$ be a real second-order stationary sequence with mean $\mu$ and autocovariances $\gamma(h) = \operatorname{Cov}(Z_0, Z_h)$ satisfying
$\sum_{h \ge 0} |\gamma(h)| < \infty$. Then

$$\operatorname{Var}\Bigl(\frac1L \sum_{i<L} Z_i\Bigr) = \frac{1}{L^2} \sum_{i, j < L} \gamma(|i - j|) \le \frac{\gamma(0) + 2\sum_{h \ge 1} |\gamma(h)|}{L},$$

so the average converges to $\mu$ in mean square and in probability. For vectors this applies coordinatewise. Genome averages of
genetic summaries over linked loci are consistent when the per-locus summaries form such a second-order stationary
sequence with summable autocovariances; it is not a central limit theorem and does not follow
from an arbitrary mixing assumption without bounds on the autocovariances.

## Sources

- P. J. Brockwell and R. A. Davis, *Time Series: Theory and Methods*, 2nd ed., Springer (1991). The bound is derived above.
