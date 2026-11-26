# Exact Gamma-mixture stationary distribution

**Setting.** Consider the bursty protein network model of [Bursty protein network model and its master equation](bursty-protein-network-model-and-its-master-equation.md): proteins $x \in \mathbb{R}_+^n$ degrade at rates $d_{1,i}$ and burst with exponential sizes of rate $c_i$ at state-dependent rates $k_{\mathrm{on},i}(x)$. Fix a finite set of basins $Z$, weights $\mu = (\mu_z)_{z \in Z}$ with $\mu_z > 0$ and $\sum_z \mu_z = 1$, and positive constants $k_{z,i}$ (the burst rate of gene $i$ in basin $z$). Write $\gamma_{z,i}(x_i)$ for the $\mathrm{Gamma}(k_{z,i}/d_{1,i}, c_i)$ density (shape $k_{z,i}/d_{1,i}$, rate $c_i$) and define the Gamma mixture

$$\hat u^{\alpha}(x) = \sum_{z \in Z} \mu_z \prod_{i=1}^n \gamma_{z,i}(x_i)$$

and the burst-rate functions

$$k^{\alpha}_{\mathrm{on},i}(x) = \frac{\sum_{z} \mu_z\, k_{z,i} \prod_{j} \gamma_{z,j}(x_j)}{\sum_{z} \mu_z \prod_{j} \gamma_{z,j}(x_j)}, \qquad i = 1, \dots, n,$$

the posterior-weighted average of the basin burst rates.

**Lemma 1 (exact stationarity).** When the burst rates are $k^\alpha_{\mathrm{on},i}$, the mixture $\hat u^\alpha$ is the stationary distribution of the bursty network model.

**Lemma 2 (impulsion bound).** Let the model be driven instead by network burst rates $k^\theta_{\mathrm{on},i}$, started from $u(0, \cdot) = \hat u^\alpha$. Then

$$\int_{\mathbb{R}_+^n} \big|\partial_t u(t, x)\big|_{t=0}\, dx \le 2\, \mathbb E_{\hat u^\alpha}\big\| k^\theta_{\mathrm{on}}(X) - k^\alpha_{\mathrm{on}}(X) \big\|_1 .$$

Thus a Gamma mixture is nearly stationary for a network $\theta$ when $k^\theta_{\mathrm{on}}$ is close to $k^\alpha_{\mathrm{on}}$ where cells are likely, which happens when burst rates are nearly constant inside each basin and $k_{z,i} = k^\theta_{\mathrm{on},i}(P_z)$ at the attractors $P_z$. Fitting the network by minimizing $\sum_{x} \sum_i \big(k^\theta_{\mathrm{on},i}(x) - k^\alpha_{\mathrm{on},i}(x)\big)^2$ over observed cells is the corresponding inference criterion for single-cell data.

## Depends on

- [Bursty protein network model and its master equation](bursty-protein-network-model-and-its-master-equation.md)

## Expansion

*Lemma 1.* In the master equation the jump terms involve $k_{\mathrm{on},i}(x)\,u(x)$, and by construction $k^\alpha_{\mathrm{on},i}(x)\, \hat u^\alpha(x) = \sum_z \mu_z k_{z,i} \prod_j \gamma_{z,j}(x_j)$. The right-hand side therefore splits into a sum over $z$ and $i$ of $\mu_z \prod_{j \ne i}\gamma_{z,j}(x_j)$ times the one-gene operator with constant rate $k_{z,i}$ applied to $\gamma_{z,i}$, namely $\partial_{x_i}(d_{1,i}x_i\gamma_{z,i}) + \int_0^{x_i} k_{z,i}\gamma_{z,i}(x_i - h)c_ie^{-c_ih}dh - k_{z,i}\gamma_{z,i}(x_i)$. Each such term vanishes because $\gamma_{z,i}$ is the stationary law of the one-gene model with constant burst rate $k_{z,i}$, so $\partial_t \hat u^\alpha = 0$.

*Lemma 2.* At $t = 0$ the master equation with $k^\theta$ applied to $\hat u^\alpha$ equals the one with $k^\alpha$ (which is zero by Lemma 1) plus the difference of jump terms, $\sum_i \big[\int_0^{x_i}(k^\theta_{\mathrm{on},i} - k^\alpha_{\mathrm{on},i})(x - he_i)\hat u^\alpha(x - he_i)c_ie^{-c_ih}dh - (k^\theta_{\mathrm{on},i} - k^\alpha_{\mathrm{on},i})(x)\hat u^\alpha(x)\big]$. Taking absolute values, integrating over $x$ and using that the exponential kernel integrates to one bounds each of the two parts by $\mathbb E_{\hat u^\alpha}|k^\theta_{\mathrm{on},i} - k^\alpha_{\mathrm{on},i}|$, giving the factor $2$.

## Sources

- E. Ventre, "Reverse engineering of a mechanistic model of gene expression using metastability and temporal dynamics", *In Silico Biology* 14(3–4) (2021) 89–113. Section 3.1 (Gamma-mixture approximation, Eq. (6)) and Appendix C (burst-rate functions, Eq. (19); Lemma 1 and Lemma 2 with proofs; regression criterion, Eq. (20)). <https://doi.org/10.3233/isb-210226>. PMCID: PMC8842760.
