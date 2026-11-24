# Closed-form weighted least-squares estimate

For a design $X$, weights $w$ and responses $z$, the closed-form weighted least-squares candidate is the generalized least-squares estimate with covariance $\operatorname{diag}(w)^{-1}$; for nonzero weights it is $(X^\top WX)^{-1}X^\top Wz$.
