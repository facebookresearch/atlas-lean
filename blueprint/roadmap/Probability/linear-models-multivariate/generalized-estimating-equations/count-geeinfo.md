# Model-based information of the count generalized estimating equation

For clusters $z = (x, y)$ with covariate vectors $x_t \in E$ (a real inner product space) and counts $y_t$ over finitely many occasions $t$, let $\mu_t(\beta) = e^{\langle x_t, \beta\rangle}$, $v(m) = m + \alpha m^2$ the negative binomial working variance with dispersion $\alpha \ge 0$, $w_t = v(\mu_t)^{-1/2}$ and $Q$ an inverse working correlation matrix. The model-based information of a cluster is $D^\top V^{-1}D : h \mapsto \sum_{s,t}Q_{st}w_sw_t\mu_s\mu_t\langle x_t, h\rangle x_s$.
