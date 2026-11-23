# BLUP as a conditional law

Let $P$ be a probability measure, let $u : \Omega \to \mathbb{R}^q$ and $e : \Omega \to \mathbb{R}^n$ be measurable and independent under $P$, with laws $N(0, G)$ and $N(0, R)$ for positive definite $G$ and $R$, and let $X$, $Z$ be real $n \times p$ and $n \times q$ matrices and $b \in \mathbb{R}^p$. Put $y = Xb + Zu + e$ and $V = Z G Z^\top + R$. Then for almost every value $y$ (with respect to the law of $y$), the conditional distribution of $u$ given $y$ is

$$N\bigl(G Z^\top V^{-1} (y - Xb),\ G - G Z^\top V^{-1} Z G\bigr)$$

(Henderson 1975; Robinson 1991).

## Sources

- C. R. Henderson, *Best linear unbiased estimation and prediction under a selection model*, Biometrics 31 (1975), 423–447.
- G. K. Robinson, *That BLUP is a good thing: the estimation of random effects*, Stat. Sci. 6 (1991), 15–32.
