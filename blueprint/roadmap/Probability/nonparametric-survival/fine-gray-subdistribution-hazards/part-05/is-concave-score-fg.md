# The weighted Fine–Gray criterion is concave

For competing-risks data with a scalar covariate $z$ and a censoring survival function $G \ge 0$, let $S_k(b, i) = \sum_lw_l(X_i)z_l^ke^{bz_l}$ with the Fine–Gray weights, $\bar z(b, i) = S_1/S_0$, $V(b, i) = S_2/S_0 - \bar z^2$, the Fine–Gray score $U(b) = \sum_{i:\varepsilon_i=c}(z_i - \bar z(b, i))$, information $I(b) = \sum_{i:\varepsilon_i=c}V(b, i)$ and criterion $\ell(b) = \sum_{i:\varepsilon_i=c}(bz_i - \log S_0(b, i))$. Then $\ell$ is a concave criterion with score $U$ and information $I$.
