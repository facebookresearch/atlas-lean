# Count generalized estimating equation score

For clusters $z = (x, y)$ with covariate vectors $x_t \in E$ (a real inner product space) and counts $y_t$ over finitely many occasions $t$, let $\mu_t(\beta) = e^{\langle x_t, \beta\rangle}$, $v(m) = m + \alpha m^2$ the negative binomial working variance with dispersion $\alpha \ge 0$, $w_t = v(\mu_t)^{-1/2}$ and $Q$ an inverse working correlation matrix. The count GEE score of one cluster is $\psi(\beta; z) = D^\top V^{-1}(y - \mu) = \sum_{s,t}Q_{st}w_sw_t\mu_s(y_t - \mu_t)x_s$.

## Sources

- K.-Y. Liang and S. L. Zeger, "Longitudinal data analysis using generalized linear models", *Biometrika* 73 (1986), 13–22.
