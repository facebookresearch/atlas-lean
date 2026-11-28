# Weight matrix of the best linear unbiased predictor

For a linear mixed model $y = X\beta + Zu + e$ with real design matrices $X$ ($n \times p$) and $Z$ ($n \times q$), a random-effect covariance $G$ and a marginal covariance $V$, let $B = (X^\top V^{-1}X)^{-1}X^\top V^{-1}$. The BLUP weight matrix for $u$ is

$$L = GZ^\top V^{-1}(I - XB),$$

with matrix inverses taken as $0$ for singular matrices.
