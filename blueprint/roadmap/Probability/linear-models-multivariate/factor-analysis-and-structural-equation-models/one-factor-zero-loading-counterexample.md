# A zero loading can destroy one-factor identification

In the standardized [one-factor model](identification-of-the-one-factor-model.md), the covariance of the observations is the outer product of the loadings plus the diagonal matrix of error variances. Loadings $(0,1,1)$ with error variances $(1,4,1)$ and loadings $(0,2,1/2)$ with error variances $(1,1,7/4)$ give the same covariance:

$$\begin{pmatrix}1&0&0\\0&5&1\\0&1&2\end{pmatrix}.$$

Both error-variance vectors are nonnegative, and neither loading vector is the other or its common negation.
