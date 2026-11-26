# Norm tail of the discrete Gaussian above the smoothing parameter

Let $0 < \varepsilon < 1$ and $s \ge \eta_\varepsilon(L)$ for a full-rank lattice $L$ in dimension $n$. For every center $v$ (Micciancio and Regev, Lemma 4.4),

$$\Pr_{x \leftarrow D_{L,s,v}}\bigl[\|x - v\| > s\sqrt{n}\bigr] \le \frac{1+\varepsilon}{1-\varepsilon}\cdot 2^{-n}.$$

## Proof sketch

Above the smoothing parameter, $\rho_{s,v}(L) \ge \frac{1-\varepsilon}{1+\varepsilon}\rho_s(L)$ by Poisson summation; combine with Banaszczyk's tail bound at $c = 1$.

## Depends on

- [Smoothing parameter of a lattice](smoothing-parameter.md)

## Proof depends on

- [Banaszczyk's shifted Gaussian tail bound](banaszczyk-shifted-gaussian-tail.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
