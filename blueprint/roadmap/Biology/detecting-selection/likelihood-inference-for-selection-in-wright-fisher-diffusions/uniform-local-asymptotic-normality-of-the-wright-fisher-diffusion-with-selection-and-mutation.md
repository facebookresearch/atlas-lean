# Uniform local asymptotic normality of the Wright–Fisher diffusion with selection and mutation

**Model.** In an infinite haploid population with two alleles, let $X_t\in[0,1]$ be the frequency of the favoured allele. Its dynamics follow the Wright–Fisher diffusion with selection and mutation

$$dX_t=\tfrac12\bigl(sX_t(1-X_t)-\theta_2X_t+\theta_1(1-X_t)\bigr)\,dt+\sqrt{X_t(1-X_t)}\,dW_t,\qquad X_0\sim\nu,$$

with parameter $\vartheta=(s,\theta_1,\theta_2)$, where $s\in\mathbb R$ is the selection coefficient and $\theta_1,\theta_2>0$ are the mutation parameters. The path is observed continuously on $[0,T]$, and $\mathbb P^{(\vartheta)}_\nu$ is its law. For $\theta_1,\theta_2>0$ the process is ergodic, with stationary density

$$f_\vartheta(x)=\frac{1}{G_\vartheta}\,e^{sx}x^{\theta_1-1}(1-x)^{\theta_2-1},\qquad x\in(0,1).$$

A process is *$\vartheta$-uniformly ergodic* if, for every compact set $\mathcal K$ of parameters, every bounded measurable $h$ and every $\varepsilon>0$,

$$\lim_{T\to\infty}\sup_{\vartheta\in\mathcal K}\mathbb P^{(\vartheta)}_\nu\Bigl[\Bigl|\tfrac1T\textstyle\int_0^T h(X_t)\,dt-\mathbb E^{(\vartheta)}h(\xi)\Bigr|>\varepsilon\Bigr]=0,\qquad \xi\sim f_\vartheta .$$

**Theorem.**

1. (Uniform ergodicity.) For every initial law $\nu$ the diffusion is $\vartheta$-uniformly ergodic on $\mathbb R\times(0,\infty)^2$.
2. (Uniform LAN.) Let $\Theta\subset\mathbb R\times[1,\infty)^2$ be open and bounded, and let the initial densities $\nu(\vartheta,\cdot)$ satisfy

$$\lim_{|\varepsilon|\to0}\frac{\nu(\vartheta+\varepsilon,x)}{\nu(\vartheta,x)}=1\quad\text{for all }x\in[0,1],$$

and, for some fixed $b\in(0,1)$ and every compact $\mathcal K\subset\Theta$, with a constant $C_{\mathcal K}>0$,

$$\sup_{\vartheta=(s,\theta_1,\theta_2)\in\mathcal K}\Bigl\{\int_0^b\frac{\max\{e^{-s},1\}}{\theta_1-1}\int_x^b\xi^{-1}(1-\xi)^{-\theta_2}\,d\xi\,\nu(\vartheta,dx)+\int_b^1\frac{\max\{e^{s},1\}}{\theta_2+1}\int_b^x\xi^{-\max\{\theta_1,2\}}\,d\xi\,\nu(\vartheta,dx)\Bigr\}\le C_{\mathcal K}.$$

Both conditions hold for $\nu=f_\vartheta$. Then the family $\{\mathbb P^{(\vartheta)}_\nu:\vartheta\in\Theta\}$ is uniformly locally asymptotically normal at rate $T^{-1/2}$. For $u\in\mathbb R^3$ with $\vartheta+u/\sqrt T\in\Theta$,

$$\log\frac{d\mathbb P^{(\vartheta+u/\sqrt T)}_\nu}{d\mathbb P^{(\vartheta)}_\nu}(X^T)=\langle u,\Delta_T(\vartheta)\rangle-\tfrac12\langle I(\vartheta)u,u\rangle+r_T(\vartheta,u),$$

where $\Delta_T(\vartheta)=T^{-1/2}\int_0^T\dot\mu(\vartheta,X_t)\,\sigma(X_t)^{-1}\,dW_t$ converges in law to $N(0,I(\vartheta))$ and $r_T\to0$ in probability, both uniformly in $\vartheta$ on compact subsets of $\Theta$. The Fisher information is

$$I(\vartheta)=\frac14\,\mathbb E^{(\vartheta)}\begin{pmatrix}\xi(1-\xi)&1-\xi&-\xi\\ 1-\xi&\frac{1-\xi}{\xi}&-1\\ -\xi&-1&\frac{\xi}{1-\xi}\end{pmatrix},\qquad \xi\sim f_\vartheta .$$

The restriction to mutation parameters at least $1$ matters. If some $\theta_i<1$, the corresponding boundary is reached in finite time, and the laws for different $\theta_i$ are mutually singular, so no likelihood ratio exists.

## Depends on

- [Martingale problem for the Wright-Fisher diffusion with selection and two-way mutation](../../population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md)

## Expansion

Uniform ergodicity follows from a general criterion for scalar diffusions on a bounded interval with regular or entrance boundaries: the two scale–speed integrals $\kappa^l_\vartheta(a,b)$ and $\kappa^r_\vartheta(a,b)$ must stay bounded away from $0$ on compacts, and for the Wright–Fisher drift they have explicit lower bounds. When $\theta_1,\theta_2\ge1$ both boundaries are entrance, and the same argument extends to the unbounded functions $(1-x)/x$ and $x/(1-x)$. These are exactly the diagonal entries of the information matrix that come from the mutation parameters. By Girsanov's formula the log-likelihood ratio is a stochastic integral minus half its quadratic variation. The martingale part gives $\Delta_T$, and uniform ergodicity applied to $\langle u,\dot\mu\rangle^2/\sigma^2$ makes the remainder vanish uniformly.

## Sources

- Jaromir Sant, Paul A. Jenkins, Jere Koskela, Dario Spanò, "Convergence of likelihood ratios and estimators for selection in nonneutral Wright–Fisher diffusions", *Scandinavian Journal of Statistics* 49 (2022), 1728–1760, <https://doi.org/10.1111/sjos.12572>; preprint arXiv:2001.03527 (2020), Definition 2.1, Theorems 2.2 and 2.3, Corollaries 2.5 and 2.6, Definition 2.7 and Theorem 2.8 (conditions (16) and (17)), <https://doi.org/10.48550/arXiv.2001.03527>.
