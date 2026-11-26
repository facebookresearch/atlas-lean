# Smoothing parameter bound from the n-th successive minimum

For every full-rank lattice $L$ in dimension $n$ and every $\varepsilon > 0$,

$$\eta_\varepsilon(L) \le \sqrt{\frac{\ln\bigl(2n(1 + 1/\varepsilon)\bigr)}{\pi}}\;\lambda_n(L),$$

where $\lambda_n(L)$ is the smallest $r$ such that $L$ contains $n$ linearly independent vectors of norm at most $r$. In particular $\eta_\varepsilon(L) \le \omega(\sqrt{\log n})\,\lambda_n(L)$ for some negligible $\varepsilon$.

## Proof sketch

Take linearly independent $v_1, \dots, v_n \in L$ of norm at most $\lambda_n$. Every nonzero dual vector $y$ has $\langle y, v_i\rangle \in \mathbb{Z}\setminus\{0\}$ for some $i$, so $L^* \setminus \{0\}$ is covered by $n$ sets on which the projection onto $v_i/\|v_i\|$ has absolute value at least $1/\lambda_n$. Bounding the Gaussian mass of each set by a one-dimensional Gaussian tail at width $1/s$ and summing over $i$ gives $\rho_{1/s}(L^*\setminus\{0\}) \le \varepsilon$ at the stated width.

## Depends on

- [Smoothing parameter of a lattice](smoothing-parameter.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
