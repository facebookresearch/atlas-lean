# Error identity of noise-free RLS

If $y_{k+1} = \varphi_k^\top \theta$ for every $k < t$ and $P_0$ is positive definite, then

$$\Big(P_0^{-1} + \sum_{k<t} \varphi_k \varphi_k^\top\Big)(\theta_t - \theta) = P_0^{-1} (\theta_0 - \theta).$$

This is the noise-free case of the error recursion (9) of Xie, Zhang and Guo, *Convergence of a distributed least squares*, IEEE Trans. Automat. Control, accepted version (2020), DOI 10.1109/TAC.2020.3047989, with a single sensor: iterating
$\tilde\theta_{k+1} = P_{k+1} P_k^{-1} \tilde\theta_k$ gives $P_t^{-1} \tilde\theta_t = P_0^{-1} \tilde\theta_0$.

## Informally uses

- [RLS solves the regularised normal equations](rls-information-mul-vec-rls-fst.md): subtract the normal equations
  satisfied by $\theta$ itself when the data are noise free.
