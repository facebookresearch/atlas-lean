# Kernel estimation of spatial modes and MBIC detection of brain-state switches

**Setting.** Data $Y_j = X(t_j) + \epsilon_j$, $j = 1, \dots, n$, follow the time-varying dynamic network $X' = A(t) X$ with $A(t) = U \Lambda(t) U^{-1}$, $\Lambda$ diagonal, piecewise constant and of rank at most $r$.

**Step 1 (smoothing).** Fit a B-spline of order $b$ with $N$ interior knots by least squares, $\hat\Gamma = \arg\min_\Gamma \sum_j \lVert Y_j - \Gamma B(t_j) \rVert_2^2$, and set $\hat X(t) = \hat\Gamma B(t)$, $\hat X'(t) = \hat\Gamma B'(t)$.

**Step 2 (local coupling matrix).** For a kernel $K_h(u) = h^{-1} K(u/h)$ with bandwidth $h$, estimate $A(t_s)$ by kernel-weighted least squares,

$$\hat A(t_s) = \arg\min_{A} \sum_{j=1}^{n} \lVert \hat X'(t_j) - A \hat X(t_j) \rVert_2^2\, K_h(t_j - t_s) = \Big[\sum_j K_h(t_j - t_s)\, \hat X'(t_j) \hat X(t_j)^{\mathsf T}\Big]\, \rho_{b_0}^{-1}\Big[\sum_j K_h(t_j - t_s)\, \hat X(t_j) \hat X(t_j)^{\mathsf T}\Big],$$

a Nadaraya–Watson type estimator in which $\rho_{b_0}^{-1}$ is the pseudo-inverse after setting singular values at most $b_0$ to zero. The threshold $b_0$ is of the order of the smoothing error of the weighted Gram matrix, and the truncation removes spurious directions when the true Gram matrix $X W X^{\mathsf T}$ ($W = \operatorname{diag} K_h(t_j - t_s)$) is rank deficient. Estimate $U$ by the eigenvectors $\hat U$ of the average $\sum_{s \in \mathcal M_S} \hat A(t_s)$ over a set $\mathcal M_S$ of time indices.

**Consistency (Theorem 1, Appendix E.2).** Under the source's regularity conditions (A1)–(A6), with $X$ of rank $q \le r$ and $U_{x,q}$ the leading $q$ left singular vectors of $X$, $\lvert \mathcal M_S \rvert = O(n)$ and $h \to 0$,

$$\Big\lVert \lvert \mathcal M_S \rvert^{-1} \sum_{s \in \mathcal M_S} \big\{ \hat A(t_s) - A(t_s) U_{x,q} U_{x,q}^{\mathsf T} \big\} \Big\rVert_F = O\big(h^2 r + n^{-1/2} N^{1/2} d\big),$$

and the leading $r$ eigenvectors $\hat U_r$ converge to those of $\sum_s A(t_s) U_{x,q} U_{x,q}^{\mathsf T}$. The $h^2 r$ term is the kernel bias and the second term is B-spline noise. When $X W X^{\mathsf T}$ has full rank the projection is the identity, so $\hat U_r \to U_r$ (Remark 1).

**Step 3 (switch detection).** Project to mode coordinates $\tilde X = (\hat U^{-1})_{r\cdot} \hat X$, $\tilde X' = (\hat U^{-1})_{r\cdot} \hat X'$. For a candidate segment, fit a diagonal $\hat \Lambda_k$ by least squares of $\tilde X'(s)$ on $\Lambda_k \tilde X(s)$, take $\hat\Sigma_k$ as the residual covariance, and let $\ell(\text{segment})$ be the negative Gaussian log-likelihood of the residuals. The number $M$ and locations $\tau$ of switches minimize

$$\mathrm{MBIC}(\tau, M) = \sum_{k=0}^{M} \ell\big((\tau_k, \tau_{k+1}]\big) + 2 r \log(n)\, \kappa\, (M + 1)$$

for a constant $\kappa$. Minimum segment length $L_{\min}$ and maximum switch count $M_{\max}$ are inputs, and the dynamic program $H(t_i \mid s) = \min_j \{ \ell((t_i, t_j]) + H(t_j \mid s - 1) \}$ evaluates all segmentations exactly in $O(r n^2 M_{\max})$ time and $O(r n M_{\max})$ storage.

## Expansion

Setting the gradient of the weighted squared residual to zero gives the normal equations $A \sum_j K_h \hat X \hat X^{\mathsf T} = \sum_j K_h \hat X' \hat X^{\mathsf T}$, hence the closed form. In the consistency proof, Taylor expansion of $A(t_s + hu)$ inside the kernel sum gives the $O(h^2)$ bias, and B-spline error expansions of $\hat X - X$ and $\hat X' - X'$ give the noise terms. Averaging over time points before the eigendecomposition pools information because $U$ does not depend on time. Projecting onto $r$ mode coordinates reduces a $d \times d$ change-point problem to $r$ diagonal parameters per segment, so exact dynamic-programming search over all segmentations stays feasible. In the source's simulations the method recovers the planted switches. On resting-state MEG it finds segments whose weighted spatial modes correlate with canonical resting-state networks more strongly than on fMRI, and on an eyes-open/eyes-closed MEG task its detected switches lie close to the hand-labeled ones.

## Depends on

- [Piecewise-constant spectral dynamics of the time-varying dynamic network](piecewise-constant-spectral-dynamics-of-the-time-varying-dynamic-network.md)

## Sources

- F. Jiang, H. Jin, Y. Gao, X. Xie, J. Cummings, A. Raj, S. Nagarajan, "Time-varying dynamic network model for dynamic resting state functional connectivity in fMRI and MEG imaging", NeuroImage 254 (2022) 119131, Sections 2.3.2–2.3.4, Eq (4), Algorithm 1, and Theorem 1 with Remark 1 (Appendix E.2), <https://doi.org/10.1016/j.neuroimage.2022.119131>, PMCID PMC9942947.
