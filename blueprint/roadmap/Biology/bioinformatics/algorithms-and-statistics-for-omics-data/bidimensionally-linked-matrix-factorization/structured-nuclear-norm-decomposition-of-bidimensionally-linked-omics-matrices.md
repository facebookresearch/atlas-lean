# Structured nuclear-norm decomposition of bidimensionally linked omics matrices

**Model.** Data blocks $\mathbf X_{ij}$ ($M_i\times N_j$) are indexed by row sets $i=1,\dots,I$ (omics platforms, features) and column sets $j=1,\dots,J$ (cancer types, samples), forming $\mathbf X_{\cdot\cdot}$ of size $M\times N$, $M=\sum M_i$, $N=\sum N_j$. The BIDIFAC+ model writes

$$\mathbf X_{\cdot\cdot}=\sum_{k=1}^K\mathbf S^{(k)}_{\cdot\cdot}+\mathbf E_{\cdot\cdot},\qquad \mathbf S^{(k)}_{ij}=\begin{cases}\mathbf U^{(k)}_i\mathbf V^{(k)T}_j&\text{if }\mathbf R[i,k]=\mathbf C[j,k]=1,\\ \mathbf 0&\text{otherwise,}\end{cases}$$

where binary indicators $\mathbf R$ ($I\times K$) and $\mathbf C$ ($J\times K$) say which platforms and which cancer types module $k$ spans (by default all $(2^I-1)(2^J-1)$ contiguous combinations), each module is low rank, and $\mathbf E$ has independent unit-variance sub-Gaussian entries after scaling. Modules are estimated by

$$\min_{\{\mathbf S^{(k)}\}}\ \tfrac12\Big\|\mathbf X_{\cdot\cdot}-\sum_k\mathbf S^{(k)}_{\cdot\cdot}\Big\|_F^2+\sum_k\lambda_k\|\mathbf S^{(k)}_{\cdot\cdot}\|_*$$

subject to the zero pattern.

**Propositions (penalties).** For every module to be estimable as non-zero it is necessary that $\lambda_k>\lambda_{k'}$ whenever module $k'$ is nested in module $k$, and $\lambda_k<\sum_{j\in\mathcal I_k}\lambda_j$ whenever modules $\mathcal I_k$ cover the rows and columns of $k$ an integer number of times. The choice

$$\lambda_k=\sqrt{\textstyle\sum_iM_i\mathbf R[i,k]}+\sqrt{\textstyle\sum_jN_j\mathbf C[j,k]},$$

the order of the largest singular value of the noise restricted to module $k$, satisfies both conditions.

**Theorem (uniqueness).** A decomposition $\{\hat{\mathbf S}^{(k)}\}$ with SVDs $\hat{\mathbf S}^{(k)}=\mathbf U^{(k)}\hat{\mathbf D}^{(k)}\mathbf V^{(k)T}$ is uniquely identified among all decompositions of the same total signal by: (1) it minimizes the structured penalty $\sum_k\lambda_k\|\mathbf S^{(k)}\|_*$; (2) for each row set $i$, the left singular vectors $\{\hat{\mathbf U}^{(k)}_i[\cdot,r]:\mathbf R[i,k]=1,\ \hat D^{(k)}[r,r]>0\}$ are linearly independent; (3) for each column set $j$, the right singular vectors $\{\hat{\mathbf V}^{(k)}_j[\cdot,r]:\mathbf C[j,k]=1,\ \hat D^{(k)}[r,r]>0\}$ are linearly independent.

The objective equals, up to constants, the negative log joint likelihood under Gaussian noise and independent Gaussian priors $\mathcal N(0,1/\lambda_k)$ on the loadings $\mathbf U^{(k)}$ and scores $\mathbf V^{(k)}$, so the solution is a posterior mode.

## Expansion

Nuclear-norm penalization soft-thresholds singular values, $\arg\min\frac12\|\mathbf X-\mathbf A\|_F^2+\lambda\|\mathbf A\|_*=\mathbf U\,\mathrm{diag}((d_r-\lambda)_+)\mathbf V^T$, and the largest singular value of an $m\times n$ noise matrix is about $\sqrt m+\sqrt n$, which motivates the module-size-dependent penalties: signal survives in a module only if it exceeds that module's noise level. Using the identity $\|\mathbf S\|_*=\min_{\mathbf S=\mathbf U\mathbf V^T}\frac12(\|\mathbf U\|_F^2+\|\mathbf V\|_F^2)$, the problem becomes a ridge-type factorization solved by alternating least squares, which handles missing blocks (e.g. a platform not measured for a cancer type) and supports imputation. Applied to pan-omics pan-cancer data, modules separate variation shared across all platforms and cancer types from variation specific to subsets.

## Sources

- Eric F. Lock, Jun Young Park and Katherine A. Hoadley, "Bidimensional linked matrix factorization for pan-omics pan-cancer analysis", The Annals of Applied Statistics 16 (2022), 193–215, <https://doi.org/10.1214/21-aoas1495>; numbering as in arXiv:2002.02601: Section 4 (model), Section 5 (objective, Propositions 1–4), Section 7 (Proposition 5, Theorem 1) and Section 8 (Propositions 6–7).
