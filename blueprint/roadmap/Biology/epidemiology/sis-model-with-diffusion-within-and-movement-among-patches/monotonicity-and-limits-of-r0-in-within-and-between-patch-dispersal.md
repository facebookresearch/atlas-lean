# Monotonicity and limits of $\mathcal{R}_0$ in within- and between-patch dispersal

**Model.** Patches $j \in \Omega = \{1, \dots, n\}$, $n \ge 2$, are bounded smooth domains $\Omega_j$. Susceptible and infected densities $S_j(x,t), I_j(x,t)$ diffuse inside patch $j$ at rates $d_{S_j}, d_{I_j} > 0$ and move between patches with uniform rates $d_S, d_I > 0$ along a connectivity matrix $L = (L_{jk})$:

$$\partial_t I_j = d_{I_j} \Delta I_j + d_I \sum_{k \ne j}\Big(\frac{L_{jk} \bar I_k}{|\Omega_j|} - L_{kj} I_j\Big) + \frac{\beta_j S_j I_j}{S_j + I_j} - \gamma_j I_j, \qquad \bar I_k = \int_{\Omega_k} I_k,$$

with the analogous equation for $S_j$ (rates $d_{S_j}, d_S$, reaction term with opposite sign) and homogeneous Neumann conditions. Assume (A0) nonnegative continuous initial data with total mass $N > 0$; (A1) $\beta_j, \gamma_j \ge 0$ Hölder continuous, $\boldsymbol\beta, \boldsymbol\gamma \ne 0$; (A2) $L$ essentially nonnegative, irreducible, with zero column sums, $L_{jj} = -\sum_{k \ne j} L_{kj}$. Total population is conserved, and by Theorem 2.2 there is a unique global bounded classical solution. Let $\boldsymbol\alpha$ be the positive eigenvector of $L$ for the eigenvalue $0$ with $\sum_j \alpha_j = 1$ (Lemma 3.1). Let $\mathcal{R}_0$ be the basic reproduction number of the model (spectral radius of its next-generation operator). Write $\bar\beta_j = \int_{\Omega_j}\beta_j$, $\bar\gamma_j = \int_{\Omega_j}\gamma_j$, and use the conventions $a/0 = 0$ if $a = 0$ and $a/0 = \infty$ if $a > 0$.

**Bounds (Lemma 5.1).** Under (A1)–(A2),

$$\inf_{x\in\bar\Omega_j,\, j\in\Omega}\frac{\beta_j(x)}{\gamma_j(x)} \le \mathcal{R}_0 \le \sup_{x\in\bar\Omega_j,\, j\in\Omega}\frac{\beta_j(x)}{\gamma_j(x)} .$$

**Theorem 5.6.** Under (A1)–(A2) (no symmetry required):

1. $\mathcal{R}_0$ is decreasing in the between-patch rate $d_I \in (0,\infty)$, strictly so if and only if $(\beta_1, \dots, \beta_n)$ is not a multiple of $(\gamma_1, \dots, \gamma_n)$;
2. $\mathcal{R}_0$ is decreasing in each within-patch rate $d_{I_j} \in (0,\infty)$;
3. the limits in slow and fast movement are

$$\lim_{\max\{d_I, d_{I_1}, \dots, d_{I_n}\}\to 0}\mathcal{R}_0 = \sup_{x\in\bar\Omega_j,\, j\in\Omega}\frac{\beta_j(x)}{\gamma_j(x)}, \qquad \lim_{\min\{d_I, d_{I_1}, \dots, d_{I_n}\}\to\infty}\mathcal{R}_0 = \frac{\sum_{j}\alpha_j \bar\beta_j/|\Omega_j|}{\sum_j \alpha_j \bar\gamma_j/|\Omega_j|} .$$

When $L$ is symmetric, Theorem 5.3 obtains the same conclusions from the variational formula

$$\mathcal{R}_0 = \sup_{\boldsymbol\varphi \in \prod_j H^1(\Omega_j),\ \boldsymbol\varphi \ne 0}\ \frac{\sum_j |\Omega_j|\int_{\Omega_j}\beta_j\varphi_j^2}{f(\boldsymbol\varphi, d_I, d_{I_1},\dots,d_{I_n}) + \sum_j |\Omega_j|\int_{\Omega_j}\gamma_j\varphi_j^2}$$

(Lemma 5.2), where $f$ is the Dirichlet-type energy of the within- and between-patch movement, increasing in each rate.

Restricting the movement of infected individuals therefore always raises (weakly) the risk of an outbreak, up to the worst local ratio $\beta/\gamma$; very fast movement averages transmission and recovery with the patch weights $\alpha_j$.

## Depends on

- [Threshold dynamics of the reaction-diffusion SIS patch model](threshold-dynamics-of-the-reaction-diffusion-sis-patch-model.md)

## Expansion

$1/\mathcal{R}_0$ is the principal eigenvalue $\tilde\lambda_1$ of $-\lambda\beta_j\varphi_j = d_{I_j}\Delta\varphi_j + d_I\sum_{k\ne j}(L_{jk}\bar\varphi_k/|\Omega_j| - L_{kj}\varphi_j) - \gamma_j\varphi_j$. Integrating this equation over each patch and summing kills the movement terms, giving the bounds. For symmetric $L$ the problem is self-adjoint in a weighted $L^2$ space and the Rayleigh quotient gives monotonicity directly. Without symmetry, the authors show that the principal eigenvalue $\lambda_1(d_I, a)$ of the auxiliary operator with reaction $a\beta_j - \gamma_j$ is decreasing in $d_I$ (strictly unless $a\beta - \gamma$ is constant), using graph-theoretic (Kirchhoff-tree) arguments for irreducible $L$; the identity $\lambda_1(d_I, \tilde\lambda_1(d_I)) = 0$ transfers this to $\tilde\lambda_1$. As rates go to $0$ the principal eigenvalue localizes at the maximum of $\beta/\gamma$; as they go to $\infty$ eigenfunctions become constant on each patch with patch masses proportional to $\boldsymbol\alpha$.

## Sources

- S. Chen, Y. Wu, "Analysis of a Reaction-Diffusion Susceptible-Infected-Susceptible Epidemic Patch Model Incorporating Movement Inside and Among Patches", arXiv:2301.06645 (2023), Lemmas 3.2, 3.3, 5.1, Theorems 2.2, 4.1, 4.2, 5.3 and 5.6, <https://doi.org/10.48550/arXiv.2301.06645>.
