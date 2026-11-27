# Large-dispersal expansion of the patch-network growth rate

**Setting.** A heterogeneous environment has $n$ patches with movement rates $m_{ij} \ge 0$ from patch $j$ to patch $i \ne j$, and the movement matrix $M = (m_{ij})$ is irreducible. Its Laplacian $L$ has diagonal entries $\ell_{jj} = \sum_{i\ne j} m_{ij}$ and off-diagonal entries $\ell_{ij} = -m_{ij}$, so every column sums to zero. Let $\boldsymbol\theta \gg 0$ be the right null vector of $L$ normalized by $\mathbf 1^\top\boldsymbol\theta = 1$. This is the dispersal equilibrium distribution, and $0 = s(-L)$ is the Perron root of $-L$. Let $L^\#$ be the group inverse of $L$, the unique matrix with $LL^\# = L^\#L$, $LL^\#L = L$, $L^\#LL^\# = L^\#$; it satisfies $LL^\# = I_n - \boldsymbol\theta\mathbf 1^\top$ and $\mathbf 1^\top L^\# = 0$. Local patch growth rates are $\mathbf q = (q_1, \dots, q_n)^\top$, $Q = \operatorname{diag}(\mathbf q)$, and the network growth rate at dispersal rate $\mu > 0$ is the spectral bound

$$r = s(Q - \mu L).$$

**Network average and heterogeneity index.**

$$\mathcal A = \sum_i q_i\theta_i = \mathbf q^\top\boldsymbol\theta, \qquad \mathcal H = \sum_{i,j} q_i\,\ell^\#_{ij}\,q_j\,\theta_j = \mathbf q^\top L^\#\operatorname{diag}(\boldsymbol\theta)\,\mathbf q .$$

**Theorem (perturbation of the Perron root).** For $\varepsilon > 0$ let $\lambda$ be the Perron root of $\varepsilon Q - L$. If $Q$ is not a multiple of $I_n$, then $\lambda = (\mathbf 1^\top Q\boldsymbol\theta)\varepsilon + (\mathbf 1^\top QL^\#Q\boldsymbol\theta)\varepsilon^2 + o(\varepsilon^2)$, with Perron vector $\boldsymbol\theta + (\alpha I_n + L^\#Q)\boldsymbol\theta\,\varepsilon + o(\varepsilon)$ for some $\alpha \in \mathbb R$. If $Q = qI_n$, then $\lambda = q\varepsilon$ exactly.

**Theorem (large-dispersal expansion).** If $Q$ is not a multiple of $I_n$, then

$$r = s(Q - \mu L) = \mathcal A + \frac{1}{\mu}\,\mathcal H + o\Big(\frac1\mu\Big) \quad (\mu \to \infty), \qquad \mathcal A \le r \le \max_i q_i .$$

If $q_1 = \dots = q_n = q$, then $r = q$. Consequently, two networks with the same network average $\mathcal A$ are ranked by $\mathcal H$: if $\mathcal H^{(1)} > \mathcal H^{(2)}$, then $r^{(1)} > r^{(2)}$ for all sufficiently large $\mu$.

**Applications.** In the multi-patch SIS model linearized at the disease-free equilibrium, $J = \operatorname{diag}(\beta_i - \gamma_i) - \mu_I L$, so the sign of $r = s(J)$ decides disease invasion, with $q_i = \beta_i - \gamma_i$. In a single-species metapopulation $x_i' = x_if_i(x_i) + \mu\sum_j(m_{ij}x_j - m_{ji}x_i)$, persistence is decided by $r = s(\operatorname{diag}(f_i(0)) - \mu L)$.

## Expansion

Write $Q - \mu L = \mu(\varepsilon Q - L)$ with $\varepsilon = 1/\mu$ and expand the simple Perron eigenpair of $\varepsilon Q - L$ in powers of $\varepsilon$ around $(0, \boldsymbol\theta)$. The first-order equation $L\boldsymbol\nu_1 = Q\boldsymbol\theta - \lambda_1\boldsymbol\theta$ is solvable only if $\lambda_1 = \mathbf 1^\top Q\boldsymbol\theta$, because $\mathbf 1^\top L = 0$. The component of $\boldsymbol\nu_1$ in $\operatorname{range}(L)$ is $L^\#Q\boldsymbol\theta$. The second-order solvability condition then gives $\lambda_2 = \mathbf 1^\top QL^\#Q\boldsymbol\theta$. Monotonicity and convexity of $r$ in $\mu$ (strict unless $Q$ is scalar) give the sharp bounds, with $r \to \max_i q_i$ as $\mu \to 0$ and $r \downarrow \mathcal A$ as $\mu \to \infty$.

## Sources

- Poroshat Yazdanbakhsh, Mark Anderson and Zhisheng Shuai, "A New Perspective on Determining Disease Invasion and Population Persistence in Heterogeneous Environments", Journal of Mathematical Biology 91 (2025), 75, <https://doi.org/10.1007/s00285-025-02302-0>; numbering as in arXiv:2410.09154: Lemma 2.1, Theorem 3.2, Corollary 3.2.1, Lemma 3.3, Theorem 3.4, Section 4 definitions of $\mathcal A$ and $\mathcal H$, Theorem 4.5, Sections 5 and 6.
