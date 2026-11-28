# Two-locus cline under strong recombination

Let $\Omega\subset\mathbb R^n$ be a bounded smooth domain. Two diallelic loci ($A/a$, $B/b$) are under additive, spatially varying selection: alleles $A$ and $B$ have Malthusian parameters $\tfrac12\alpha(x)$ and $\tfrac12\beta(x)$, and $a$, $b$ have $-\tfrac12\alpha(x)$, $-\tfrac12\beta(x)$. With diffusion scaled to one, selection strength $\lambda>0$ and recombination rate $\rho=1/\varepsilon$, the allele frequencies $p_A,p_B$ and the linkage disequilibrium $D=p_{AB}-p_Ap_B$ evolve by

$$ \partial_t p_A=\Delta p_A+\lambda\alpha p_A(1-p_A)+\lambda\beta D,\quad \partial_t p_B=\Delta p_B+\lambda\beta p_B(1-p_B)+\lambda\alpha D,\quad \partial_t D=\Delta D+2\nabla p_A\cdot\nabla p_B+\lambda[\alpha(1-2p_A)+\beta(1-2p_B)]D-\varepsilon^{-1}D $$

with homogeneous Neumann boundary conditions. Assume (A): $\alpha,\beta\in C^\gamma(\bar\Omega)$ both change sign in $\Omega$. For $h\in\{\alpha,\beta\}$ let $\theta_h$ be the globally attracting equilibrium of the one-locus equation $\partial_t\theta=\Delta\theta+\lambda h\theta(1-\theta)$ (Neumann data), and let $\lambda_A=\lambda_\alpha$, $\lambda_B=\lambda_\beta\in(0,\infty)$ be the thresholds above which this one-locus equilibrium is a non-constant cline: $\lambda_h=\lambda^*(h)$ if $\bar h<0$, $\lambda_h=\lambda^*(-h)$ if $\bar h>0$ and $\lambda_h=0$ if $\bar h=0$, where $\lambda^*(h)$ is the positive value of $\lambda$ for which $\Delta\varphi+\lambda h\varphi=0$ has a positive Neumann solution.

**Theorem.** For every $\lambda>0$ with $\lambda\neq\max\{\lambda_A,\lambda_B\}$ and all sufficiently small $\varepsilon>0$ there is an equilibrium $(\hat p_A^{(\varepsilon)},\hat p_B^{(\varepsilon)},\hat D^{(\varepsilon)})$ attracting every trajectory whose initial data have no locus fixed, with convergence in $C^2(\bar\Omega)^3$. Moreover:

- if $0<\lambda<\max\{\lambda_A,\lambda_B\}$, there is no internal equilibrium, and the attractor is $(\theta_\alpha,\theta_\beta,0)$, in which at least one locus is fixed;
- if $\lambda>\max\{\lambda_A,\lambda_B\}$, the attractor is internal (a two-locus cline, all four gametes present) and

$$ \|(\hat p_A^{(\varepsilon)},\hat p_B^{(\varepsilon)})-(\theta_\alpha,\theta_\beta)\|_{C^1(\bar\Omega)}+\|\hat D^{(\varepsilon)}\|_{C(\bar\Omega)}=O(\varepsilon). $$

So under strong recombination a two-locus cline exists, is unique and is globally asymptotically stable exactly when both single-locus clines exist, and it is a small perturbation of their product in linkage equilibrium.

## Depends on

- [Haldane's cline in a step environment](../../../haploid-selection-and-multiplicative-fitnesses/stationary-cline-in-a-step-environment.md)

## Expansion

Recombination erodes $D$ at rate $1/\varepsilon$. A gradient estimate $|\nabla p_A|\le C_0\,p_A(1-p_A)$ (and likewise for $B$), uniform in $\varepsilon$, gives $\limsup_t\|D\|_\infty=O(\varepsilon)$, together with sharper bounds on the coupling terms $\lambda\beta D$ and $\lambda\alpha D$ in terms of the gradient of the other locus. With $D\approx0$ the two allele-frequency equations decouple into one-locus reaction–diffusion problems with indefinite weight, whose global attractors are known. Below $\max\{\lambda_A,\lambda_B\}$ one locus is driven to fixation, after which $D\to0$ and the other locus settles on its single-locus attractor; above it, a perturbation argument around $(\theta_\alpha,\theta_\beta,0)$ plus the uniform a priori bounds yields existence, uniqueness and global attraction of the internal equilibrium.

## Sources

- Linlin Su, King-Yeung Lam and Reinhard Bürger, "Two-locus clines maintained by diffusion and recombination in a heterogeneous environment", *J. Differential Equations* 266(12) (2019), 7909–7947. <https://doi.org/10.1016/j.jde.2018.12.022>
- Preprint version (the locators in this item follow its numbering): L. Su, K.-Y. Lam and R. Bürger, "Two-locus clines maintained by diffusion and recombination in a heterogeneous environment", arXiv:1808.03665 (2018), <https://doi.org/10.48550/arXiv.1808.03665>. Theorem 7.1 (strong recombination), with the model in Section 2 and the one-locus theory in Theorem 3.4.
