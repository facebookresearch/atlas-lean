# Smoothing parameter bound from the dual first minimum

For every full-rank lattice $L$ in dimension $n$, with $\lambda_1(L^*)$ the length of a shortest nonzero dual vector,

$$\eta_{2^{-n}}(L) \le \frac{\sqrt{n}}{\lambda_1(L^*)}.$$

## Proof sketch

At width $s = \sqrt n/\lambda_1(L^*)$ every nonzero dual vector has norm at least $\sqrt{n}/s$ relative to width $1/s$, so its Gaussian mass lies in the tail; Banaszczyk's tail bound on $L^*$ bounds $\rho_{1/s}(L^* \setminus\{0\})$ by $2^{-n}$.

## Depends on

- [Smoothing parameter of a lattice](smoothing-parameter.md)

## Proof depends on

- [Banaszczyk's shifted Gaussian tail bound](banaszczyk-shifted-gaussian-tail.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
