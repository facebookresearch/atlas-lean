# Unbiasedness with covariates

Let a [first-moment SLDP model](model.md) on a measure $P$ have mean effects $m = \mu v + U\gamma$, where $\mu \in \mathbb{R}$, $v \in \mathbb{R}^M$, $U$ is a real $M \times K$ matrix of background annotations ($K$ a finite set) and $\gamma \in \mathbb{R}^K$ is arbitrary. Let $X$ be a real $N \times M$ genotype matrix with [in-sample LD matrix](ld-matrix.md) $\hat R$, put $A = \hat R U$, let $W$ be a symmetric real $M \times M$ matrix, and let $w \in \mathbb{R}^K$ be such that the residual $z = \hat R v - A w$ satisfies $A^\top W z = 0$. If $z^\top W z \ne 0$, then

$$\int \frac{z^\top W \hat\alpha}{z^\top W z} \, dP = \mu,$$

where $\hat\alpha$ is the vector of [normalized marginal scores](alpha-hat.md). When $W$ is positive semidefinite, the integrand is the coefficient of $\hat R v$ in the joint weighted least-squares regression of $\hat\alpha$ on $[A \mid \hat R v]$.
