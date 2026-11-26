# Weighted risk-set mean

For real weights $Y_l$ and a scalar covariate $z_l$, the weighted mean is $\bar z(b) = S^{(1)}(b)/S^{(0)}(b) = \sum_lY_lz_le^{bz_l}\big/\sum_lY_le^{bz_l}$, each subject weighted by $Y_le^{bz_l}$ and the total divided by $\sum_lY_le^{bz_l}$, taken as $0$ when $S^{(0)}(b) = 0$. When each $Y_l$ is the indicator that subject $l$ is at risk, this is the $e^{bz}$-weighted mean of the covariate over the risk set, and $S^{(0)}(b) = 0$ exactly when the risk set is empty.
