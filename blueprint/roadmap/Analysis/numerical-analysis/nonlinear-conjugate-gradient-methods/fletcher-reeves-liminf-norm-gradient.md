# Global convergence of the Fletcher–Reeves method under strong Wolfe steps

Let $f$ be a function on a finite-dimensional real inner product space whose level set
$\{y : f(y) \le f(x_0)\}$ is bounded and which, on an open neighbourhood $U$ of it, is
differentiable with $L$-Lipschitz gradient. Run $x_{k+1} = x_k + \alpha_k d_k$ with
$d_0 = -\nabla f(x_0)$ and

$$d_{k+1} = -\nabla f(x_{k+1}) + \frac{\|\nabla f(x_{k+1})\|^2}{\|\nabla f(x_k)\|^2}\, d_k ,$$

every step length $\alpha_k > 0$ satisfying the
[strong Wolfe conditions](../line-search-methods/strong-wolfe-conditions.md) with
$0 < \delta < \sigma \le 1/2$. If no gradient vanishes, then $\liminf_k \|\nabla f(x_k)\| = 0$.

The bound $\sigma \le 1/2$ is what makes every Fletcher–Reeves direction a descent direction
(Lemma 4.1 of the source, whose proof it refers to Al-Baali). Al-Baali (1985) proved the
convergence for $\sigma < 1/2$; the endpoint $\sigma = 1/2$ is due to Liu, Han and Yin (1993) and to
Dai and Yuan (1996). Compare the
[Dai–Yuan method](dai-yuan-liminf-norm-gradient.md), which needs only standard Wolfe steps.

## Background

- [Zoutendijk condition](../line-search-methods/zoutendijk.md): the summability (Lemma 2.2 of the
  source) on which its general convergence criteria, Lemmas 2.3 and 3.1, rest.

## Sources

- Y. H. Dai and Y. Yuan, *A note on the nonlinear conjugate gradient method*, J. Comput. Math. 20 (2002); https://lsec.cc.ac.cn/pub/yyx/papers/jcm1290.pdf, Theorem 4.2 under Assumption 2.1.
- M. Al-Baali, *Descent property and global convergence of the Fletcher–Reeves method with inexact
  line search*, IMA J. Numer. Anal. 5 (1985), 121–124 (the case $\sigma < 1/2$).
- G. H. Liu, J. Y. Han and H. X. Yin, *Global convergence of the Fletcher–Reeves algorithm with an
  inexact line search*, report, Institute of Applied Mathematics, Chinese Academy of Sciences (1993),
  and Y. H. Dai and Y. Yuan, *Convergence properties of the Fletcher–Reeves method*, IMA J. Numer.
  Anal. 16 (1996), 155–164 (the case $\sigma = 1/2$); references as listed in Dai and Yuan,
  SIAM J. Optim. 10 (1999).
