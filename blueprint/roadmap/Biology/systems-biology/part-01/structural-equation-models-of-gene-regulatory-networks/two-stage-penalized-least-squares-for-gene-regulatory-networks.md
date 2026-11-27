# Two-stage penalized least squares for gene regulatory networks

Let $Y \in \mathbb{R}^{n\times p}$ be expression levels of $p$ genes and $X \in \mathbb{R}^{n \times q}$ genotypes in $n$ individuals, related by the system of structural equations

$$Y = Y\Gamma + X\Psi + \epsilon,$$

where $\Gamma$ ($p\times p$, zero diagonal) holds regulatory effects, possibly forming cycles, $\Psi$ holds cis-eQTL effects, $X$ is independent of $\epsilon$, and errors are Gaussian. The reduced form is $Y = X\pi + \xi$ with $\pi = \Psi(I-\Gamma)^{-1}$, $\xi = \epsilon(I - \Gamma)^{-1}$. Assume (A) each gene $k$ has a nonempty set $\mathcal{S}_k$ of cis-eQTL with $\mathcal{S}_j \cap \mathcal{S}_k = \emptyset$ for $j \ne k$ (a rank condition guaranteeing identification), and (B) $n^{-1}X^\top X \to C \succ 0$. For gene $k$,

$$Y_k = Y_{-k}\gamma_k + X_{\mathcal{S}_k}\psi_{\mathcal{S}_k} + \epsilon_k,$$

and since $Y_{-k}$ is correlated with $\epsilon_k$, one regresses instead on $Z_{-k} = E(Y_{-k} \mid X) = X\pi_{-k}$.

**2SPLS.** Stage 1: for each gene $j$ fit the reduced form by ridge regression, $\hat\pi_j = (X^\top X + \tau_j I)^{-1}X^\top Y_j$, with $\tau_j$ chosen by generalized cross-validation, and set $\hat Z_j = X\hat\pi_j$. Stage 2: with $H_k = I - X_{\mathcal{S}_k}(X_{\mathcal{S}_k}^\top X_{\mathcal{S}_k})^{-1}X_{\mathcal{S}_k}^\top$, estimate

$$\hat\gamma_k = \arg\min_{\gamma}\ \tfrac12 (Y_k - \hat Z_{-k}\gamma)^\top H_k (Y_k - \hat Z_{-k}\gamma) + \lambda_k\, \omega_k^\top |\gamma|,$$

an adaptive lasso with weights $\omega_{kj} \propto |\tilde\gamma_{kj}|^{-\delta}$ from a $\sqrt n$-consistent pilot estimate.

**Theorem (GCV tuning).** If the entries of $\pi_j$ are i.i.d. with mean zero and variance $\sigma_\pi^2$, the minimizers over $\tau > 0$ of the expected GCV criterion and of the expected loss $\|Z_j - P_\tau Y_j\|^2$ coincide and equal $\sigma_{\xi_j}^2/\sigma_\pi^2$.

**Theorem (oracle property, fixed $p, q$).** Let $\mathcal{A}_k = \{j \ne k : \gamma_{kj} \ne 0\}$ and $M_k = \pi_{-k}^\top\big(C - C_{\cdot \mathcal{S}_k} C_{\mathcal{S}_k \mathcal{S}_k}^{-1} C_{\mathcal{S}_k \cdot}\big)\pi_{-k}$. Under (A), (B), $\tau_j/n \to 0$, $\lambda_k/\sqrt n \to 0$ and $\lambda_k n^{(\delta - 1)/2} \to \infty$,

$$\Pr(\hat{\mathcal{A}}_k = \mathcal{A}_k) \to 1, \qquad \sqrt n\,(\hat\gamma_{k,\mathcal{A}_k} - \gamma_{k,\mathcal{A}_k}) \xrightarrow{d} N\big(0,\ \sigma_k^2 M_{k,\mathcal{A}_k}^{-1}\big).$$

When $p \asymp q = o(n)$ diverge, non-asymptotic bounds hold with high probability for the ridge first stage, for the $\ell_1$ error of $\hat\gamma_k$ under a restricted-eigenvalue condition, and for exact support recovery under an irrepresentable-type condition.

## Depends on

- [Linear moment model for instrumental variables](../../../statistical-genetics/mendelian-randomization/linear-moment-model.md)
- [Closed form of ridge regression](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/ridge-le-ridge-estimate.md)

## Expansion

Because $Z_{-k}$ is a function of $X$, it is independent of the composite error $\epsilon_k + \xi_{-k}\gamma_k$, which is the instrumental-variables view of classical two-stage least squares; any consistent first-stage estimate of $Z_{-k}$ then gives consistent second-stage estimates in low dimensions. Ridge regression keeps the first stage well defined when $p \ge n$, and Theorem 5.2-type convergence $n^{-1}\hat Z_{-k}^\top H_k \hat Z_{-k} \to M_k$ lets the adaptive-lasso oracle argument go through as if the true conditional expectations were observed. Fitting one limited-information equation per gene parallelizes across genes and avoids the memory cost of full-information likelihoods.

## Sources

- C. Chen, M. Ren, M. Zhang and D. Zhang, "A two-stage penalized least squares method for constructing large systems of structural equations", Journal of Machine Learning Research 19 (2018), Sections 2–5, Eqs. (1)–(8), Assumptions A–D and Theorems 5.1–5.6, PMCID: PMC13229399, <https://pmc.ncbi.nlm.nih.gov/articles/PMC13229399/>.
