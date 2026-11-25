# Variance factor of a contrast

For a design matrix $X$ and a contrast vector $a$, the variance factor of the contrast $a^\top \hat\beta$,
where $\hat\beta$ is the least-squares estimate, is $q = a^\top (X^\top X)^{-1} a$; here the inverse of a
singular matrix is taken to be $0$. When $X^\top X$ is invertible and the errors are uncorrelated with
common variance $\sigma^2$, $\mathrm{Var}(a^\top \hat\beta) = \sigma^2 q$ (stated here without proof).
