# Matrix criterion of a linear predictor

For real matrices $Z$ ($n \times q$), $G$ ($q \times q$), $V$ ($n \times n$) and a linear predictor $C$ ($q \times n$), the matrix criterion of $Cy$ as a predictor of $u$ is

$$C V C^\top - C Z G - G Z^\top C^\top + G.$$

It is the covariance of the prediction error $Cy - u$ when $\operatorname{Cov} y = V$, $\operatorname{Cov} u = G$, $\operatorname{Cov}(y, u) = ZG$ and $\operatorname{Cov}(u, y) = GZ^\top$; these are not part of the definition.
