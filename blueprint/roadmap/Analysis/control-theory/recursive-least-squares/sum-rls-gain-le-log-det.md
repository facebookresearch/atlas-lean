# Logarithmic bound on the accumulated RLS gains

For positive definite $P_0$, with $P_k$ the RLS matrix,

$$\sum_{k<t} \frac{\varphi_k^\top P_k \varphi_k}{1 + \varphi_k^\top P_k \varphi_k} \le
\log \det\Big(P_0^{-1} + \sum_{k<t} \varphi_k \varphi_k^\top\Big) - \log \det P_0^{-1}.$$

No assumption is made on the regressors. Since $\log \det (P_0^{-1} + \sum_{k<t} \varphi_k \varphi_k^\top) \le
d \log \lambda_{\max}$, the accumulated gains grow at most logarithmically in the size of the data; this is the
deterministic inequality behind the $O(\log r_t)$ terms of the stochastic theory.

Source: the single-sensor case of inequality (33) of Xie, Zhang and Guo, *Convergence of a distributed least squares*,
IEEE Trans. Automat. Control, accepted version (2020), DOI 10.1109/TAC.2020.3047989, whose proof follows Lai and Wei
(Ann. Statist. 10 (1982)).

## Informally uses

- [Multiplicative matrix determinant lemma for invertible matrices](../../../LinearAlgebra/determinants-and-matrix-identities/matrix-determinant-lemma/det-add-vec-mul-vec-of-is-unit-det.md):
  $\det P_{k+1}^{-1} = \det P_k^{-1} \, (1 + \varphi_k^\top P_k \varphi_k)$, so each term is
  $q / (1 + q) \le \log(1 + q)$ with $q = \varphi_k^\top P_k \varphi_k \ge 0$, and the sum telescopes.
- [The RLS matrix is the inverse of the information matrix](rls-snd-eq-inv.md): $P_k^{-1}$ is the information matrix.
