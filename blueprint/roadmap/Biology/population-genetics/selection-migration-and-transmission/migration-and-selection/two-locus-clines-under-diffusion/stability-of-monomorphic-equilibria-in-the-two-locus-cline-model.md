# Stability of monomorphic equilibria in the two-locus cline model

Consider gamete frequencies $p_1,\dots,p_4$ (gametes $AB,Ab,aB,ab$) of two diallelic loci in a bounded smooth habitat $\Omega\subset\mathbb R^n$ under diffusion (scaled to one), additive spatially varying selection of strength $\lambda>0$ and recombination at rate $\rho\ge0$:

$$ \partial_t p_i=\Delta p_i+\lambda p_i(w_i-\bar w)-\eta_i\rho D,\qquad \partial_\nu p_i=0,\qquad i=1,\dots,4, $$

where $\eta_1=\eta_4=-\eta_2=-\eta_3=1$, $D=p_1p_4-p_2p_3$, $w_i=\sum_j w_{ij}p_j$, $\bar w=\sum_i w_ip_i$, and the genotype fitnesses are $w_{ij}=s_i+s_j$ with gamete coefficients $s_1=\tfrac12(\alpha+\beta)$, $s_2=\tfrac12(\alpha-\beta)$, $s_3=-s_2$, $s_4=-s_1$. Assume (A): $\alpha,\beta\in C^\gamma(\bar\Omega)$ change sign in $\Omega$, and the generic condition that some gamete $i$ has strictly the largest spatial average, $\bar s_i>\bar s_j$ for both gametes $j$ that share exactly one allele with $i$. Let $M_j$ be the monomorphic equilibrium with gamete $j$ fixed everywhere.

**Theorem.** For every $\rho\ge0$:

- every $M_j$ with $j\neq i$ is linearly unstable;
- there is a critical selection strength $\lambda_i^*(\rho)\in(0,\infty)$, the smallest of the principal-eigenvalue thresholds of the linearization at $M_i$, such that $M_i$ is linearly stable for $0<\lambda<\lambda_i^*(\rho)$ and linearly unstable for $\lambda>\lambda_i^*(\rho)$.

The threshold $\lambda_i^*(\rho)$ is nondecreasing in $\rho$, so stronger recombination enlarges the range of selection-to-diffusion ratios over which fixation of the gamete with the highest mean fitness is stable. In the non-generic case where two gametes share the largest average and the other two the smallest, all monomorphic equilibria are linearly unstable for every $\rho\ge0$. In the unscaled model (diffusion $d$, selection $s$, recombination $r$), for fixed $r\ge0$ and $s>0$, $M_i$ is globally asymptotically stable once $d$ is large enough.

## Expansion

At $M_j$ the linearization decouples: each gamete $k$ sharing an allele with $j$ gives a scalar Neumann problem $\Delta\phi+\lambda h\phi+\mu\phi=0$ with indefinite weight $h=s_k-s_j$, while the complementary gamete $\tilde j$ is also fed by recombination and contributes eigenvalues shifted by $+\rho$. For an indefinite weight with $\bar h<0$ the principal eigenvalue is positive for small $\lambda$ and negative beyond a threshold; for $\bar h\ge0$ it is negative for all $\lambda>0$. Only the gamete with the largest spatial average has all its weights with negative mean, which gives instability of the other vertices and a finite threshold for $M_i$. The shift by $\rho$ raises the threshold coming from the complementary gamete, hence the monotonicity in $\rho$.

## Sources

- Linlin Su, King-Yeung Lam and Reinhard Bürger, "Two-locus clines maintained by diffusion and recombination in a heterogeneous environment", *J. Differential Equations* 266(12) (2019), 7909–7947. <https://doi.org/10.1016/j.jde.2018.12.022>
- Preprint version (the locators in this item follow its numbering): L. Su, K.-Y. Lam and R. Bürger, "Two-locus clines maintained by diffusion and recombination in a heterogeneous environment", arXiv:1808.03665 (2018), <https://doi.org/10.48550/arXiv.1808.03665>. Theorem 4.4 and Remark 4.5 (stability threshold and its monotonicity in recombination), Proposition 4.8 (degenerate case), Theorem 4.6 (large diffusion), with the model in Section 2.
