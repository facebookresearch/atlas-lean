# Single-edge path weight equals partial covariance over one minus squared vector correlation

**Setting.** Let $X_V$ be a random vector (e.g. expression levels of genes $V$) with positive definite covariance $\Sigma$ and concentration matrix $K=\Sigma^{-1}=(\kappa_{uv})$, and let $\mathcal G=(V,E)$ be the undirected graph implied by $K$: $\{u,v\}\in E$ iff $\kappa_{uv}\neq0$. For a path $\pi$ in $\mathcal G$ with vertex set $P$ define the **path weight**

$$
w(\pi,\Sigma)=(-1)^{|P|+1}\,|\Sigma_{PP}|\prod_{\{u,v\}\in E(\pi)}\kappa_{uv}=(-1)^{|P|+1}\,\frac{|K_{\bar P\bar P}|}{|K|}\prod_{\{u,v\}\in E(\pi)}\kappa_{uv},
$$

with $\bar P=V\setminus P$ and $|K_{\emptyset\emptyset}|=1$. For disjoint $A,B\subseteq V$ the **vector alienation coefficient** is $\lambda_{A.B}=|\Sigma_{A\cup B,A\cup B}|/(|\Sigma_{AA}||\Sigma_{BB}|)=\prod_i(1-\varrho_i^2)$ over the canonical correlations $\varrho_i$, and the **vector correlation** is $\rho_{A.B}=\sqrt{1-\lambda_{A.B}}$.

**Theorem (covariance decomposition over paths, Jones and West; Theorem 2.1).** For all $x,y\in V$, $\sigma_{xy}=\sum_{\pi\in\Pi_{xy}}w(\pi,\Sigma)$, where $\Pi_{xy}$ is the set of all paths from $x$ to $y$ in $\mathcal G$.

**Theorem (Theorem 3.1).** For every edge $\{x,y\}\in E$, with $R=V\setminus\{x,y\}$,

$$
w(\langle x,y\rangle,\Sigma)=\frac{\sigma_{xy\mid R}}{1-\rho^2_{\{x,y\}.R}} ,
$$

where $\sigma_{xy\mid R}$ is the partial covariance of $X_x,X_y$ given $X_R$. This quantity $\omega_{xy\mid R}$ is the **networked partial covariance**; normalizing gives the **networked partial correlation**

$$
\psi_{xy\mid R}=\frac{\omega_{xy\mid R}}{\sqrt{\sigma_{xx\mid R}\,\sigma_{yy\mid R}}}=\frac{\rho_{xy\mid R}}{1-\rho^2_{\{x,y\}.R}},\qquad \rho_{xy\mid R}=\frac{-\kappa_{xy}}{\sqrt{\kappa_{xx}\kappa_{yy}}} .
$$

Thus $\omega_{xy\mid R}$ vanishes exactly when the edge is absent, has the sign of the partial covariance, satisfies $|\omega_{xy\mid R}|\ge|\sigma_{xy\mid R}|$, and equals $\sigma_{xy\mid R}$ when the pair $\{x,y\}$ is uncorrelated with the rest of the network. It may exceed $1$ in absolute value.

## Expansion

For the single-edge path, $P=\{x,y\}$ and $w=-|\Sigma_{PP}|\kappa_{xy}$. The partial covariance matrix of $X_P$ given $X_R$ is $(K_{PP})^{-1}$, so $\sigma_{xy\mid R}=-\kappa_{xy}/|K_{PP}|$ and $|\Sigma_{PP\mid R}|=1/|K_{PP}|$. Hence $w=\sigma_{xy\mid R}\,|\Sigma_{PP}|/|\Sigma_{PP\mid R}|$. By the Schur complement $|\Sigma|=|\Sigma_{RR}|\,|\Sigma_{PP\mid R}|$, so $|\Sigma_{PP\mid R}|/|\Sigma_{PP}|=|\Sigma|/(|\Sigma_{PP}||\Sigma_{RR}|)=\lambda_{P.R}=1-\rho^2_{P.R}$, which is the claim. In the yeast application, networked partial correlations of coexpressed gene pairs estimated by limited-order versions of the decomposition separate genetically interacting pairs better than marginal or ordinary partial correlations.

## Sources

- A. Roverato and R. Castelo, "The networked partial correlation and its application to the analysis of genetic interactions", arXiv:1510.02510 (2015), Section 2 (path weights, vector correlation, Theorem 2.1) and Section 3 (Theorem 3.1, networked partial correlation), <https://doi.org/10.48550/arXiv.1510.02510>.
