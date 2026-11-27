# GCTA's REML equations at a local maximizer with positive variances

Let $m$ and $r$ be finite index sets, $K$ a real $m \times m$ matrix, $B$ a real $r \times m$
matrix with $BB^\top = I$ and $BKB^\top = \operatorname{diag}(d)$, and $y \in \mathbb{R}^m$. Let
$\theta = (\sigma_g^2, \sigma_e^2)$ be a local maximizer in $\mathbb{R}^2$ of
$\varphi \mapsto \ell_B(\varphi)$, the restricted log-likelihood of $y$ for $B$ at
$V(\varphi) = \varphi_1 K + \varphi_2 I$ (the logarithm of the density of the Gaussian law
$N(0, B V(\varphi) B^\top)$ at $By$), at which every [contrast variance](contrast-var.md)
$\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$ is positive. Then, with the
[REML projection](reml-proj.md) $P = B^\top (B V(\theta) B^\top)^{-1} B$,

$$y^\top P K P y = \operatorname{tr}(P K), \qquad y^\top P P y = \operatorname{tr} P.$$
