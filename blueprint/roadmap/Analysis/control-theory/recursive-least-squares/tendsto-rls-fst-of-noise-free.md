# Convergence of noise-free RLS under growing excitation

Let $P_0$ be positive definite and let the data be noise free, $y_{k+1} = \varphi_k^\top \theta$ for every $k$. If the
smallest eigenvalue of $\sum_{k<t} \varphi_k \varphi_k^\top$ tends to infinity, written as: for every $M$, eventually
$M |x|^2 \le x^\top \big(\sum_{k<t} \varphi_k \varphi_k^\top\big) x$ for all $x$, then $\theta_t \to \theta$ for
every initial estimate $\theta_0$. Persistent excitation, $\lambda_{\min}(\sum_{k<t} \varphi_k \varphi_k^\top) \ge c t$
for some $c > 0$, is a special case; in the noise-free case no rate condition relating the largest and smallest
eigenvalues is needed.

## Informally uses

- [Error bound of noise-free RLS under excitation](rls-error-sq-le.md): the error is at most
  $|P_0^{-1}(\theta_0 - \theta)| / M$ once the smallest eigenvalue exceeds $M$.
