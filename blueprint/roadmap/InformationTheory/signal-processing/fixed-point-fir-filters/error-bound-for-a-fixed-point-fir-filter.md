# Error bound for a fixed-point FIR filter

Fix an integer $q \ge 0$, put $\varepsilon = 2^{-q-1}$, and let $\rho(u) = 2^{-q} \lfloor 2^q u + \tfrac12 \rfloor$ be rounding to the grid
$2^{-q}\mathbb Z$, half up, so that $|\rho(u) - u| \le \varepsilon$. For real coefficients $h_0, \dots, h_{m-1}$ and inputs
$x_0, \dots, x_{m-1}$ let $y = \sum_k h_k x_k$. The fixed-point filter with range bound $M > 0$ computes the grid values
$\hat h_k = \rho(h_k)$, $\hat x_k = \rho(x_k)$, the rounded products $\hat p_k = \rho(\hat h_k \hat x_k)$ and the left fold
$\hat a_0 = 0$, $\hat a_{k+1} = \rho(\hat a_k + \hat p_k)$, and raises an overflow flag if any of these values has absolute value
greater than $M$; its output is $\hat y = \hat a_m$. If the flag is not raised, then

$$|\hat y - y| \le \varepsilon \sum_k |h_k| + \varepsilon \sum_k |x_k| + m\,\varepsilon^2 + m\,\varepsilon .$$

Sums of grid values are grid values, so $\hat a_{k+1} = \hat a_k + \hat p_k$ exactly and $\hat y = \sum_k \hat p_k$; each term
satisfies $|\hat p_k - h_k x_k| \le |h_k|\varepsilon + |x_k|\varepsilon + \varepsilon^2 + \varepsilon$, from
$\hat h_k \hat x_k - h_k x_k = h_k(\hat x_k - x_k) + x_k(\hat h_k - h_k) + (\hat h_k - h_k)(\hat x_k - x_k)$.

## Sources

- A. V. Oppenheim and R. W. Schafer, *Discrete-Time Signal Processing*, 3rd edition, Pearson, 2010, Chapter 6 (finite-precision numerical effects in digital filters).
