# Law of large numbers for the stochastic Wilson–Cowan neural field

**Macroscopic model.** On a bounded domain $D\subset\mathbb R^d$ with Lipschitz boundary, the Wilson–Cowan neural field is

$$\tau\,\partial_t\nu(t,x)=-\nu(t,x)+f\Bigl(\int_D w(x,y)\nu(t,y)\,dy+I(t,x)\Bigr),$$

with $\tau>0$, $w\in L^2(D\times D)$, input $I$, and a gain function $f\ge 0$ that is bounded and globally Lipschitz.

**Microscopic model.** For each $n$, partition (most of) $D$ into $P(n)$ subdomains $D_{k,n}$, the $k$-th holding $l(k,n)$ neurons of which $\Theta^{k,n}_t$ are active. With averaged weights $\bar W^n_{kj}=|D_{k,n}|^{-1}\int_{D_{k,n}}\int_{D_{j,n}}w(x,y)\,dy\,dx$, averaged input $\bar I_{k,n}(t)$ and activation rate $\bar f_{k,n}(\theta,t)=f\bigl(\sum_j\bar W^n_{kj}\theta_j/l(j,n)+\bar I_{k,n}(t)\bigr)$, the count $\theta_k$ decreases by one at rate $\theta_k/\tau$ and increases by one at rate $l(k,n)\bar f_{k,n}/\tau$. Embed the process in $L^2(D)$ by $\nu^n_t=\sum_k\frac{\Theta^{k,n}_t}{l(k,n)}\mathbf 1_{D_{k,n}}$. Let $\delta_+(n)$ be the largest diameter of a subdomain, $v_-(n)=\min_k|D_{k,n}|$ and $v_+(n)=\max_k|D_{k,n}|$ the smallest and largest subdomain volumes, and $\ell_-(n)=\min_k l(k,n)$ and $\ell_+(n)=\max_k l(k,n)$ the smallest and largest population sizes.

**Theorem (law of large numbers).** Assume $I\in L^2_{\mathrm{loc}}(\mathbb R_+,H^1(D))$, $\nu^n_0\to\nu(0)$ in probability in $L^2(D)$, $\mathbb E\,\Theta^{k,n}_0\le l(k,n)$, and

$$\lim_{n\to\infty}\delta_+(n)=0,\qquad\lim_{n\to\infty}\ell_-(n)=\infty .$$

Then for all $T,\epsilon>0$,

$$\lim_{n\to\infty}\mathbb P\Bigl[\sup_{t\in[0,T]}\|\nu^n_t-\nu(t)\|_{L^2(D)}>\epsilon\Bigr]=0,$$

and if moreover $\sup_n\mathbb E\|\nu^n_0\|^{2r}_{L^2(D)}<\infty$ for some $r\ge 1$, then $\mathbb E\sup_{t\le T}\|\nu^n_t-\nu(t)\|^r_{L^2(D)}\to 0$. Under additional regularity of $I$, the convergence in mean holds uniformly over all $t\ge 0$ in the weaker norm of $H^{-\alpha}(D)$, $\alpha\ge 0$.

**Fluctuations.** Writing $\nu^n_t=\nu^n_0+\int_0^t(\text{drift})\,ds+M^n_t$, for $\alpha>d$, under the hypotheses of the theorem with convergence in mean for $r=1$, and if the patch volumes and sizes are asymptotically balanced,

$$\lim_{n\to\infty}\frac{v_-(n)}{v_+(n)}\,\frac{\ell_-(n)}{\ell_+(n)}=1,$$

the rescaled martingales $\sqrt{\ell_-(n)/v_+(n)}\,M^n$ converge weakly in the space of $H^{-\alpha}(D)$-valued càdlàg paths to a centred Gaussian diffusion, which yields a Langevin approximation of the neural field.

## Proof depends on

- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Expansion

The proof compares the martingale decomposition of $\nu^n$ with the integral form of the Wilson–Cowan equation. Each jump changes $\nu^n$ by $\pm l(k,n)^{-1}\mathbf 1_{D_{k,n}}$, so the quadratic variation of $M^n$ is of order $1/\ell_-(n)$ and the martingale vanishes; the drift differs from the Wilson–Cowan vector field by spatial averaging errors controlled by $\delta_+(n)$ via the Poincaré inequality, and Lipschitz continuity of $f$ with Gronwall's inequality closes the estimate. The limit does not depend on the exact microscopic rates: replacing $f$ by any $f_n\to f$ uniformly gives the same law of large numbers.

## Sources

- M. G. Riedler and E. Buckwar, "Laws of large numbers and Langevin approximations for stochastic neural field equations", Journal of Mathematical Neuroscience 3 (2013) 1, <https://doi.org/10.1186/2190-8567-3-1>, PMCID PMC3582461. Eqs. (1.3)–(1.4), (2.4)–(2.11) and (2.15), Theorems 2.1–2.3.
