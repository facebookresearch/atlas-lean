# Error bound of noise-free RLS under excitation

Let $P_0$ be positive definite and $y_{k+1} = \varphi_k^\top \theta$ for $k < t$. If $M > 0$ is a lower bound for the
smallest eigenvalue of $\sum_{k<t} \varphi_k \varphi_k^\top$, in the form
$M |x|^2 \le x^\top \big(\sum_{k<t} \varphi_k \varphi_k^\top\big) x$ for all $x$, then

$$|\theta_t - \theta|^2 \le \frac{|P_0^{-1} (\theta_0 - \theta)|^2}{M^2}$$

(Euclidean norms).

## Informally uses

- [Error identity of noise-free RLS](rls-information-mul-vec-error-of-noise-f.md): with $e = \theta_t - \theta$ and
  $c = P_0^{-1}(\theta_0 - \theta)$, $M |e|^2 \le e^\top (P_0^{-1} + \sum_k \varphi_k \varphi_k^\top) e = e^\top c
  \le |e| \, |c|$.
