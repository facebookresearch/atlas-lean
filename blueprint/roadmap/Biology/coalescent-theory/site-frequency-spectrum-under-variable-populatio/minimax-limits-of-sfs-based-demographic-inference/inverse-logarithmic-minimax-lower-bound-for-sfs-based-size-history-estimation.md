# Inverse-logarithmic minimax lower bound for SFS-based size-history estimation

**Setting.** Data are the derived-allele counts at $s$ independent segregating sites in a sample of $n$ individuals, drawn i.i.d. from the SFS distribution $q^{(\eta)}_n$ of Kingman's coalescent with population-size history $\eta$, normalized by $\eta(0)=N_0$ (histories related by $\zeta(t)=\kappa\,\eta(t/\kappa)$ give the same SFS). An estimator $\hat\eta$ is any map from the empirical SFS to a size history; the loss is the truncated $L_1$ distance

$$
\|\eta_a-\eta_b\|_{1,T}=\int_0^T|\eta_a(t)-\eta_b(t)|\,dt .
$$

For $\varepsilon,\delta>0$ let $\mathcal M_{I,J}(\varepsilon,\delta)$ be the bottleneck family of $2^J$ piecewise-constant histories (identical for the first $I$ epochs, minimum size $\varepsilon$ attained in epoch $I$ of duration $t_b$, then nondecreasing steps of size $0$ or $\delta$ at change points spaced $t_a$ apart), with $I$, $t_b$ and $t_a$ fixed. A fixed such family has distinct SFS distributions, so its minimax risk tends to $0$ exponentially fast in $s$; the bounds below hold for the families taken over all step sizes and bottleneck sizes, which the proofs choose depending on $s$. Let $\mathcal M_{I,J}=\bigcup_{\delta>0}\mathcal M_{I,J}(\varepsilon,\delta)$ for a given $\varepsilon$, and $\mathcal M^M_{I,J}=\{\eta\in\bigcup_{\varepsilon,\delta>0}\mathcal M_{I,J}(\varepsilon,\delta):\|\eta\|_\infty<M\}$.

**Theorem (non-asymptotic bound).** If $J>8$ and $T\ge t_{I+J-1}+t_a$, then

$$
\inf_{\hat\eta}\sup_{\eta\in\mathcal M_{I,J}}\mathbb{E}_\eta\|\hat\eta-\eta\|_{1,T}\ge C\,t_a\,\frac{(J-8)^2}{J}\,\frac{\varepsilon}{s}\,e^{t_b/\varepsilon}
$$

for a positive constant $C$.

**Theorem (bounded histories).** If $J>8$ and $T\ge t_{I+J-1}+t_a$, then

$$
\inf_{\hat\eta}\sup_{\eta\in\mathcal M^M_{I,J}}\mathbb{E}_\eta\|\hat\eta-\eta\|_{1,T}\ge C'\,\frac{(J-8)^2}{J}\,\frac{t_b\,t_a}{\log s}.
$$

**Corollary.** With $\mathcal M^M_{I,\star}=\bigcup_{J\ge1}\mathcal M^M_{I,J}$ and $T\ge t_{I+J-1}+t_a$,

$$
\inf_{\hat\eta}\sup_{\eta\in\mathcal M^M_{I,\star}}\mathbb{E}_\eta\|\hat\eta-\eta\|_{1,T}\ge C''\,(T-t_I)\,\frac{t_b}{\log s}.
$$

The minimax rate is therefore at best $1/\log s$, exponentially slower than the parametric $s^{-1/2}$ rate, and the bounds do not depend on $n$: for a fixed number of segregating sites, sequencing more individuals does not reduce the minimax error.

## Depends on

- [KL divergence bound between SFS distributions of size histories](kl-divergence-bound-between-sfs-distributions-of-size-histories.md)

## Expansion

Fano's method: if $r$ hypotheses are pairwise $\alpha_r$-separated in the loss and have pairwise KL divergence at most $\beta_r$ per observation, then any estimator from $s$ observations has worst-case risk at least $\frac{\alpha_r}{2}\big(1-\frac{s\beta_r+\log2}{\log r}\big)$. By the Varshamov–Gilbert bound, $\mathcal M_{I,J}$ contains $r\ge2^{J/8}$ histories whose step patterns differ in at least $J/8$ positions, giving $L_1$ separation of order $J\delta t_a$, while the KL divergence is at most $J(\delta/\varepsilon)e^{-t_b/\varepsilon}$. Choosing $\delta=(J-8)\log2\cdot(\varepsilon/s)e^{t_b/\varepsilon}/(16J)$ keeps $s\beta_r$ below a fraction of $\log r$ and yields the first bound. For bounded histories, $\delta$ cannot exceed $M$; taking the bottleneck size $\varepsilon$ of order $t_b/\log s$ makes $\varepsilon e^{t_b/\varepsilon}/s$ of order one and gives the $t_bt_a/\log s$ rate. Taking $J$ proportional to $(T-t_I)/t_a$ gives the corollary.

## Sources

- Jonathan Terhorst and Yun S. Song, *Fundamental limits on the accuracy of demographic inference based on the sample frequency spectrum*, *Proceedings of the National Academy of Sciences* 112 (2015), 7677–7682, <https://doi.org/10.1073/pnas.1503717112>; preprint arXiv:1505.04228, <https://doi.org/10.48550/arXiv.1505.04228>. Numbering of the arXiv version: Theorems 4, 5 and 7 (Fano's method), Corollary 6.
