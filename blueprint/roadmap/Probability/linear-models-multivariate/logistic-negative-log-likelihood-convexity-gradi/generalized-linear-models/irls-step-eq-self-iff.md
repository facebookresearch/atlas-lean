# Fixed points of iteratively reweighted least squares are score roots

For a design $X$, responses $y$, a mean function $\mu$ and a weight function $V$, write $\eta = X\beta$, $W(\beta) = \operatorname{diag}(V(\eta_i))$, the working response $z_i = \eta_i + (y_i - \mu(\eta_i))/V(\eta_i)$, and let the IRLS step be the weighted least-squares fit of $z$ on $X$ with weights $V(\eta_i)$. If the weights at $\beta$ are nonzero and $X^\top W(\beta)X$ is invertible, the IRLS step fixes $\beta$ if and only if $X^\top(y - \mu(X\beta)) = 0$.
