# Storey's q-value

Let $\mathrm{pfdr} : \mathbb{R} \to \mathbb{R}$, where $\mathrm{pfdr}(s)$ is the positive false discovery rate of the region $\Gamma_s = \{T \le s\}$ of a nested family of rejection regions. Storey's q-value of an observed statistic $t$ is

$$q(t) = \inf_{s \ge t} \mathrm{pfdr}(s),$$

the smallest pFDR over the regions that contain $t$; it is $0$ by convention when $\{\mathrm{pfdr}(s) : s \ge t\}$ is unbounded below.

## Sources

- J. D. Storey, *The positive false discovery rate: a Bayesian interpretation and the q-value*, Ann. Statist. 31 (2003), 2013–2035.
