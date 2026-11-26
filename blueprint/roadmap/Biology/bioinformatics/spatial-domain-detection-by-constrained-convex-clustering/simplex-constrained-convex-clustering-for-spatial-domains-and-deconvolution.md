# Simplex-constrained convex clustering for joint spatial domain detection and cell-type deconvolution

**Model.** In spot-based spatial transcriptomics, expression $x_{gi}$ of gene $g$ in spot $i$ satisfies

$$\mathbb E(X_{gi}\mid V_i=v_i)=s_i^*\,b_g^\top v_i,\qquad \mathbb E(V_i)=\theta_i^*\in\Delta^{K-1},$$

where $b_g\in\mathbb R_+^K$ is the mean expression of gene $g$ in $K$ reference cell types (from single-cell data), $V_i$ the realized cell-type composition of the spot, $\theta_i^*$ its *expected* composition, $s_i^*\ge0$ a size factor (roughly the number of cells), and $\Delta^{K-1}$ the probability simplex. A **spatial domain** is a maximal set of spots sharing the same expected composition $\theta_c^\ddagger$. Conditional distributions may be normal, Poisson or negative binomial; spots and genes are treated as independent for the working likelihood, whose score remains unbiased whenever the first moment is correct.

**Estimator.** With $\mathcal F_i(\theta,s)=-\log f(x_i;\theta,s)$ the working negative log-likelihood of spot $i$ and spatial weights $\gamma_{ij}\ge0$,

$$(\widehat\Theta^\lambda,\widehat S^\lambda)=\arg\min_{\Theta,S}\ \frac1n\sum_{i=1}^n\mathcal F_i(\theta_i,s_i)+\lambda\sum_{i<j}\gamma_{ij}\|\theta_i-\theta_j\|_2\quad\text{s.t. }\theta_i\in\Delta^{K-1},\ s_i\ge0 .$$

The fused group penalty sets nearby compositions exactly equal, so a single tuning parameter $\lambda$ controls both the number of domains and spatial smoothness, tracing a path from spot-by-spot deconvolution ($\lambda=0$) to a single domain. At $\lambda=0$ in the normal case each spot reduces to nonnegative least squares in $\rho_i=s_iv_i$.

**Proposition (fusion threshold).** Let $(\bar\theta,\bar s)$ minimize the single-domain problem $\sum_i\mathcal F_i(\theta,s_i)$ over $\theta\in\Delta^{K-1}$, $s_i\ge0$, put $\bar\Theta=\mathbf 1_n\bar\theta^\top$, and let $G=\nabla_\Theta\frac1n\sum_i\mathcal F_i(\bar\theta,\bar s_i)$. If the weighted incidence matrix $D$ of the spot graph encodes a connected graph, then $\bar\Theta$ solves the problem (with $S=\bar S$) for every $\lambda\ge\lambda_{\mathrm{trivial}}$, where

$$\lambda_{\mathrm{trivial}}=\min_{V,\eta,\nu}\|V\|_{2,\infty}\quad\text{s.t.}\quad D^\top V=-G-\eta\mathbf 1_K^\top+\nu,\ \ \nu\ge0,\ \ \nu_{ik}=0\text{ on }\operatorname{supp}(\bar\theta),$$

with $\|V\|_{2,\infty}=\max_\ell\|V_{\ell\cdot}\|_2$. This is a second-order cone program and attains its minimum, so the solution path can be computed on $[0,\lambda_{\mathrm{trivial}}]$.

## Expansion

The threshold is a KKT certificate: at $\bar\Theta$ all differences vanish, so the penalty's subgradient is $D^\top V$ with each edge row of norm at most $\lambda\gamma_{ij}$-scaled one; the simplex constraint contributes a multiplier $\eta$ for the sum-to-one equality and $\nu\ge0$ for coordinates at zero. Stationarity requires the loss gradient to be balanced by these terms, and the smallest $\lambda$ for which such $V$ exists is the SOCP value. Connectivity guarantees that the incidence matrix spans all differences, so any gradient orthogonal to constants can be balanced. The model-based loss lets the same criterion handle counts or normalized data, and characterizing each domain by its expected cell-type mix makes the detected domains biologically interpretable.

## Sources

- Hyun Jung Koo, Aaron J. Molstad, "Constrained convex clustering for interpretable spatial domain detection in spot-based spatial transcriptomics", arXiv:2511.06204 (2025): Section 2.1 (model assumptions), Section 2.2 (penalized M-estimation criterion), Section 4.2 and Proposition 1 (fusion threshold). <https://doi.org/10.48550/arXiv.2511.06204>
