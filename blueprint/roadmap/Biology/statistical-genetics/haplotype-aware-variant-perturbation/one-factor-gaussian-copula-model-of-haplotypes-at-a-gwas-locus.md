# One-factor Gaussian copula model of haplotypes at a GWAS locus and its identifiability

**Problem.** At a GWAS locus with lead variant $0$ and linked partner variants $1,\dots,k$, sequence-to-function models are usually queried by editing only the lead allele on the reference genome, which silently fixes every partner at its reference allele and may create a haplotype that is rare or absent in the population. The goal is to rank partner configurations $x\in\{0,1\}^k$ by $\Pr(X=x\mid X_0=s)$ for each lead allele $s$.

**Model.** With alternate-allele frequencies $p_j\in(0,1)$, thresholds $\tau_j=\Phi^{-1}(1-p_j)$ and a latent Gaussian vector,

$$X_j=\mathbf 1\{Z_j>\tau_j\},\qquad Z_{ij}=\mathbf b_j^\top f_i+\varepsilon_{ij},\qquad f_i\sim\mathcal N_q(0,I_q),\quad \varepsilon_i\sim\mathcal N_p\big(0,\operatorname{diag}(\psi)\big),$$

with $\|\mathbf b_j\|^2+\psi_j=1$, so $\operatorname{corr}(Z)=\mathbf R=\mathbf B\mathbf B^\top+\operatorname{diag}(\psi)$ and $\Pr(X_j=1)=p_j$ exactly (fixed margins). Given the factor the variants are independent, $\Pr(X_j=1\mid f)=\Phi\big((\mathbf b_j^\top f-\tau_j)/\sqrt{\psi_j}\big)$, so

$$\Pr(X=x\mid X_0=s)=\int_{\mathbb R^q}p(f\mid X_0=s)\prod_{j=1}^k\Pr(X_j=x_j\mid f)\,df,\qquad p(f\mid X_0=s)\propto\phi_q(f)\Pr(X_0=s\mid f),$$

reducing a sum over $2^k$ configurations to a $q$-dimensional integral. $\mathbf B$ is identified only up to $O(q)$, but haplotype probabilities and rankings are invariant.

**Proposition (identifiability with one factor).** Take $q=1$ and parameters $(\mathbf b,\tau)$ with every $\psi_j=1-b_j^2\in(0,1]$. Then:
1. $(\mathbf b,\tau)$ and $(-\mathbf b,\tau)$ induce the same law of $X$;
2. if at least three coordinates of $\mathbf b$ are nonzero and $(\mathbf b',\tau')$ induces the same law, then $\tau'=\tau$ and $\mathbf b'=\pm\mathbf b$;
3. if moreover $b_0\neq0$, the normalization $b_0>0$ selects a unique representative, and then every partner with $b_j\neq0$ has $\operatorname{sign}(b_j)=\operatorname{sign}(R_{0j})$, the sign of its latent correlation with the lead.

So under one factor the loadings are recovered up to a global reflection, and fixing the lead's sign makes each partner's allele association with the lead interpretable.

## Expansion

Margins fix $\tau$. Under one factor the latent correlations are $R_{jl}=b_jb_l$ for $j\neq l$, and each pairwise tetrachoric probability determines $R_{jl}$ strictly monotonically; with three nonzero loadings $b_j^2=R_{jl}R_{jm}/R_{lm}$ determines every $|b_j|$, and the signs of the $R_{jl}$ determine $\mathbf b$ up to one global sign. The ranking step evaluates the one-dimensional integral for candidate configurations; under strong linkage disequilibrium the dominant configuration is recovered exactly in simulations, while a misspecified single factor leaves residual correlation that a higher $q$ absorbs. In an Alzheimer's-disease benchmark the haplotype-aware inputs enriched recovery of microglial eQTLs relative to lead-only edits.

## Sources

- Jichun Xie, "HaploPerturb: Low-rank copula construction of haplotype perturbations improves sequence-to-function analysis of Alzheimer's disease loci", arXiv:2608.05002 (2026): Section 3.1 (perturbation problem), Section 3.2 (latent Gaussian factor model and Proposition 1), Sections 3.3–5 (ranking and validation), Section 6 (eQTL benchmark). <https://doi.org/10.48550/arXiv.2608.05002>
