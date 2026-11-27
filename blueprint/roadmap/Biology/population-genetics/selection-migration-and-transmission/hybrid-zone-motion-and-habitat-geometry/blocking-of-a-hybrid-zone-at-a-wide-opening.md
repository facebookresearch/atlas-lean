# Blocking of a hybrid zone at a wide opening

**Model.** Consider a diploid population with alleles $a,A$ in which $aa$ is fitter than $AA$ and both are fitter than the heterozygote $aA$. In the large-selection scaling the frequency $u^\epsilon(x,t)$ of $a$ solves the unbalanced Allen–Cahn equation

$$\partial_tu^\epsilon=\Delta u^\epsilon+\frac1{\epsilon^2}u^\epsilon(1-u^\epsilon)\big(2u^\epsilon-(1-\nu\epsilon)\big)\ \ (x\in\Omega,\ t>0),\qquad \partial_nu^\epsilon=0\ \text{on }\partial\Omega,\qquad u^\epsilon(x,0)=\mathbf 1_{\{x_1\ge0\}},$$

with $\nu>0$ the selective advantage of $aa$ over $AA$ and $\Omega\subset\mathbb R^d$ ($d\ge2$) a cylinder-like domain $\Omega=\{(x_1,x'):x'\in\phi(x_1)\}$. The *hybrid zone* is the thin layer where $u^\epsilon\in(\delta,1-\delta)$; as $\epsilon\to0$ it moves by mean curvature plus a constant normal velocity $\nu$, meeting $\partial\Omega$ at right angles. Take first the isthmus domain: cross-section $\{\|x'\|<r_0\}$ for $x_1>0$ (the channel where type $a$ starts) and $\{\|x'\|<R_0\}$ for $x_1<0$, with $r_0<R_0$.

**Theorem (blocking).** If $r_0<\frac{d-1}{\nu}\wedge R_0$, fix $\bar r\in(r_0,R_0)$ and let $\hat d(x)$ be the signed distance to the hemispherical cap $N_{\bar r}=\{x\in\Omega:\|x\|=\bar r,\ x_1<0\}$ (negative towards $x_1=-\infty$). For every $k$ there are $\hat\epsilon(k),M(k)>0$ such that for $\epsilon<\hat\epsilon$ and **all** $t\ge0$: $\hat d(x)\le-M\epsilon|\log\epsilon|\Rightarrow u^\epsilon(x,t)\le\epsilon^k$. The advantageous type never passes the opening.

**Theorem (invasion).** If $r_0>\frac{d-1}{\nu}$, then for every $x\in\Omega$ and $\delta>0$ there are $\hat t$ and $\hat\epsilon$ with $u^\epsilon(x,t)\ge1-\delta$ for all $\epsilon<\hat\epsilon$, $t\ge\hat t$.

**Theorem (general widening).** If $\phi(x_1)=\{\|x'\|\le H+h(-x_1)\}$ with $h>0$ of class $C^1$, then

$$\inf_{z>0}\Big\{H+h(z)-\frac{d-1}{\nu}\,\frac{h'(z)}{\sqrt{1+h'(z)^2}}\Big\}<0$$

implies blocking (there is $x_0<0$ with $u^\epsilon\le\epsilon^k$ for $x_1\le x_0-M\epsilon|\log\epsilon|$, all $t$), while the same infimum being $>0$ implies complete invasion.

## Expansion

The interface pushed out of the channel tries to spread into the wide region as a spherical cap. Its normal velocity is $\nu-\kappa$, where for a cap of radius $r$ in $\mathbb R^d$ the mean curvature is $\kappa=(d-1)/r$; the forces balance at $r^*=(d-1)/\nu$. If the channel radius $r_0$ is below $r^*$, the cap emerging from the channel is too curved to advance, and a stationary hemispherical barrier of radius between $r_0$ and $R_0$ exists; comparison with sub- and supersolutions built from the one-dimensional travelling wave profile around such caps traps $u^\epsilon$ uniformly in time. Unlike on all of $\mathbb R^d$, where a sphere of radius $r^*$ is unstable, the blocking is robust because the interface is pinned at the wall. In the general widening domain, the criterion compares the local channel radius with $r^*$ times the sine of the wall slope. The paper also treats a stochastic version driven by a spatial $\Lambda$-Fleming–Viot process with selection and identifies the strength of genetic drift under which the hybrid zone structure persists or breaks down.

## Sources

- Alison M. Etheridge, Mitchell D. Gooding and Ian Letter, "On the effects of a wide opening in the domain of the (stochastic) Allen-Cahn equation and the motion of hybrid zones", Electron. J. Probab. 27 (2022), 1–53, <https://doi.org/10.1214/22-EJP888>. Numbering follows the arXiv version, arXiv:2204.00316 (2022): Section 1.1 (equation $(AC_\epsilon)$, Theorems 1.6, 1.7, 1.9 and 1.10) and Section 1.2 (Definition 1.13, Theorems 1.17 and 1.19), <https://doi.org/10.48550/arXiv.2204.00316>.
