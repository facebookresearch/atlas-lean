# Dirichlet–multinomial residuals for jointly overdispersed counts

**Setting.** A count matrix $X=(X_{ij})$ has samples $i$ (cells, libraries) and features $j=1,\dots,K$ (genes, peaks), with sample totals $n_i=\sum_jX_{ij}$. The Dirichlet–multinomial $\mathrm{DM}(n,\boldsymbol\alpha)$, $\alpha_0=\sum_j\alpha_j$, has pmf $\frac{n!\,\Gamma(\alpha_0)}{\Gamma(n+\alpha_0)}\prod_j\frac{\Gamma(x_j+\alpha_j)}{x_j!\,\Gamma(\alpha_j)}$.

**Theorem 2.1.** If $X_{ij}\sim\mathrm{Poi}(\lambda_{ij})$ independently, then $(X_{i1},\dots,X_{iK})\mid n_i\sim\mathrm{Mult}\big(n_i,(\lambda_{ij}/\sum_\ell\lambda_{i\ell})_j\big)$.

**Theorem 2.2.** If $X_{ij}\sim\mathrm{NegBin}(r_j,p_i)$ independently, with $\Pr(X_{ij}=x)=\frac{\Gamma(x+r_j)}{\Gamma(r_j)\Gamma(x+1)}(1-p_i)^xp_i^{r_j}$, then $(X_{i1},\dots,X_{iK})\mid n_i\sim\mathrm{DM}(n_i,\mathbf r)$; the sample-specific $p_i$ drops out.

**DM residual.** Fix a global composition $\boldsymbol\pi$ and concentration $\alpha_0$. The row-level contrast $\Delta_i=\log\Pr_{\mathrm{DM}(n_i,\alpha_0X_i/n_i)}(X_i)-\log\Pr_{\mathrm{DM}(n_i,\alpha_0\boldsymbol\pi)}(X_i)$ splits as $\Delta_i=\sum_jc_{ij}$ with
$$c_{ij}=\sum_{m=0}^{X_{ij}-1}\log\frac{\alpha_0X_{ij}/n_i+m}{\alpha_0\pi_j+m},\qquad d_{ij}=\operatorname{sgn}(X_{ij}-n_i\pi_j)\sqrt{|c_{ij}|}.$$
Zero counts give $c_{ij}=0$, so the transform preserves sparsity.

**Properties.**
- (Proposition 2.3) Unrestricted DM saturation collapses to the multinomial: $\sup_{\boldsymbol\alpha>0}\Pr_{\mathrm{DM}(n,\boldsymbol\alpha)}(x)=\Pr_{\mathrm{Mult}(n,x/n)}(x)$, which is why the concentration must be held fixed.
- (Proposition 2.4) If $X_{ij}=1$, $d_{ij}$ equals the multinomial residual $\operatorname{sgn}(1-n_i\pi_j)\sqrt{|\log(1/(n_i\pi_j))|}$.
- (Propositions 2.5–2.6) For fixed nonzero $X_{ij}=x$, $c_{ij}\to x\log\frac{x}{n_i\pi_j}$ (the multinomial term) as $\alpha_0\to\infty$, and the DM shrinks large-count residuals toward zero relative to it.
- (Proposition 2.7, Corollary 2.8) Independent negative-binomial likelihoods factor as $\Pr_{\mathrm{NB}(\alpha_0,p_i)}(n_i)\cdot\Pr_{\mathrm{DM}(n_i,\alpha_0\boldsymbol\pi)}(X_i\mid n_i)$, so with $p_i=\alpha_0/(n_i+\alpha_0)$ the feature-wise negative-binomial contrast equals the DM contrast.

## Expansion

Theorem 2.2 is the gamma–Poisson construction: $\mathrm{NegBin}(r_j,p_i)$ is Poisson with a $\mathrm{Gamma}(r_j)$ rate scaled by a common factor; conditioning independent gammas on their sum gives a Dirichlet independent of the sum, and conditioning Poissons on their total gives a multinomial, so the composition is DM with parameters $\mathbf r$. The closed form of $c_{ij}$ uses $\log\{\Gamma(x+a)/\Gamma(a)\}=\sum_{m=0}^{x-1}\log(a+m)$: all normalizing terms that depend only on $n_i$ and $\alpha_0$ cancel between numerator and denominator, leaving a sum of $X_{ij}$ terms per nonzero entry. Increments of the sum shrink as $m$ grows, which is the shrinkage of repeated counts; as $\alpha_0\to\infty$ each summand tends to $\log(X_{ij}/(n_i\pi_j))$.

## Sources

- A. Balsubramani, "Deviance-style normalization for jointly overdispersed counts", arXiv preprint (2026), Theorems 2.1–2.2, Propositions 2.3–2.7 and Corollary 2.8, <https://doi.org/10.48550/arXiv.2606.26061>.
