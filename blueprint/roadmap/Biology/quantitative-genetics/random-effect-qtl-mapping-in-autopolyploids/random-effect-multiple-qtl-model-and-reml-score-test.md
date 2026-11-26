# Random-effect multiple-QTL model and REML score test

For a full-sib family of $n$ autopolyploid individuals with phenotype vector $y$, let $G_1, \dots, G_Q$ be the [IBD relationship matrices](genotype-classes-and-ibd-relationship-matrix-of-an-autopolyploid-full-sib-family.md) at $Q$ putative QTL. The random-effect multiple interval mapping (REMIM) model is

$$y = \mathbf 1\mu + \sum_{q=1}^{Q} g_q + \varepsilon, \qquad g_q \sim N(0, G_q\sigma_q^2), \quad \varepsilon \sim N(0, I\sigma^2),$$

with independent random terms, equivalently $y = \mathbf 1\mu + \sum_q Z_q u_q + \varepsilon$ with $u_q \sim N(0, \Pi\sigma_q^2)$ over the $p$ genotype classes. Then $\mathbb E\,y = \mathbf 1\mu$ and $\operatorname{Var}(y) = \sum_q G_q \sigma_q^2 + I\sigma^2$, and only one variance component per QTL is estimated whatever the ploidy.

To test $H_0: \tau_r = 0$ against $\tau_r > 0$ for a QTL $r$, with $\sigma_q^2 = \sigma^2\tau_q$ and $V(\tau) = G_r\tau_r + \sum_{q\ne r} G_q\tau_q + I$, choose an $(n-1)\times n$ matrix $A$ with $A\mathbf 1 = 0$ and $AA^\top = I_{n-1}$, and set $\tilde y = Ay$, $\tilde G_q = AG_qA^\top$, $\tilde V = A V A^\top$, $\tilde n = n - 1$. The REML log-likelihood profiled over $\sigma^2$ is

$$\ell(\tau) = -\tfrac12\Bigl\{\tilde n \log\bigl(\tilde y^\top \tilde V(\tau)^{-1}\tilde y\bigr) + \log\det \tilde V(\tau)\Bigr\} + \text{const},$$

and the score for $\tau_r$ is

$$S_r(\tau) = \frac{\partial \ell}{\partial \tau_r} = \frac{\tilde n}{2}\,\frac{\tilde y^\top \tilde V^{-1}\tilde G_r \tilde V^{-1}\tilde y}{\tilde y^\top \tilde V^{-1}\tilde y} - \frac12 \operatorname{tr}\bigl(\tilde V^{-1}\tilde G_r\bigr).$$

**Proposition.** With a single QTL in the model ($Q = r = 1$), $\tilde V(0) = I_{\tilde n}$ and

$$S_1(0) = \frac{\tilde n}{2}\,\frac{\tilde y^\top \tilde G_1 \tilde y}{\tilde y^\top \tilde y} - \frac12\operatorname{tr}\tilde G_1,$$

whose null distribution is exact: under $H_0$, $\tilde y/\|\tilde y\|$ is uniform on the unit sphere of $\mathbb R^{\tilde n}$, so $S_1(0)$ is a fixed affine function of a ratio of quadratic forms in a standard normal vector and does not depend on $\mu$ or $\sigma^2$. With further QTL as nuisance components, a moment-based approximation to the null distribution is used.

## Depends on

- [Genotype classes and IBD relationship matrix of an autopolyploid full-sib family](genotype-classes-and-ibd-relationship-matrix-of-an-autopolyploid-full-sib-family.md)

## Expansion

Since $A\mathbf 1 = 0$, $\tilde y \sim N(0, \sigma^2 \tilde V(\tau))$ is free of $\mu$; maximizing the Gaussian log-likelihood of $\tilde y$ over $\sigma^2$ gives $\hat\sigma^2 = \tilde y^\top\tilde V^{-1}\tilde y/\tilde n$ and the profiled form. Differentiating with $\partial \tilde V/\partial\tau_r = \tilde G_r$, $\partial \tilde V^{-1} = -\tilde V^{-1}\tilde G_r \tilde V^{-1}$ and $\partial\log\det\tilde V = \operatorname{tr}(\tilde V^{-1}\tilde G_r)$ gives $S_r$. Under $H_0$ with one QTL, $\tilde y = \sigma\tilde\varepsilon$ with $\tilde\varepsilon \sim N(0, I_{\tilde n})$, and the ratio is scale-invariant. In the source, QTL are added in rounds by forward search over a 1 cM grid of stored $G_q$, with $P$-values of the score reported as $-\log_{10} P$.

## Sources

- G. da Silva Pereira, D. C. Gemenet, M. Mollinari et al., "Multiple QTL mapping in autopolyploids: a random-effect model approach with application in a hexaploid sweetpotato full-sib population", Genetics (2020), <https://doi.org/10.1534/genetics.120.303080>, PMCID PMC7337090 (equations (3)–(4), REML profile and score statistic following Qu et al. 2013).
