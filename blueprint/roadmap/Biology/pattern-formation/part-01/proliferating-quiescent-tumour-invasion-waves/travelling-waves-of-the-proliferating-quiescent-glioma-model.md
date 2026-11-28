# Travelling waves of the proliferating–quiescent glioma model

**Model.** Let $p(x,t)$ and $q(x,t)$ be the densities of proliferating and quiescent (functionally necrotic) tumour cells, normalised so that $p+q\le 1$, and let $w=1-p-q$ be the free space or available growth factor. In one space dimension the model is the cross-diffusion system

$$\partial_t p=\partial_x\!\Big[\tfrac{Dp}{p+q}\,\partial_x(p+q)\Big]+\rho\,g(w)\,p-k\,\delta(w)\,p,\qquad
\partial_t q=\partial_x\!\Big[\tfrac{Dq}{p+q}\,\partial_x(p+q)\Big]+k\,\delta(w)\,p,$$

with $D,\rho,k>0$. The birth and quiescence functions satisfy

$$g'(w)\ge0,\quad \delta'(w)\le0,\quad g(1)=1,\ \delta(1)=0,\quad g(0)=0,\ \delta(0)=1,$$

so birth grows and quiescence shrinks with available growth factor, there is only birth when $w=1$, and only quiescence when $w=0$. Rescaling $x=\sqrt{D/k}\,\hat x$, $t=\hat t/k$ leaves the single parameter $\hat\rho=\rho/k$.

**Minimal speed.** Seek waves $p(\hat x-c\hat t)$, $q(\hat x-c\hat t)$. Linearising at the leading edge with $p=Ae^{-r\xi}$, $q=Be^{-r\xi}$ ($A,B,r>0$) gives $r^2-cr+\hat\rho=0$, which has a positive real root only when $c^2\ge4\hat\rho$. The minimal speed is $c_{\min}=2\sqrt{\hat\rho}$, or $2\sqrt{\rho D}$ in dimensional units, the Fisher–KPP speed with the birth rate $\rho$ at full growth factor in place of the net growth rate.

**Reduced profile and its existence.** With $z=-\xi/c$ and the terms of order $1/c^2$ dropped (Canosa's approximation), the profile satisfies

$$\frac{dp}{dz}=p\,\big(\hat\rho\,g(w)-\delta(w)\big),\qquad \frac{dw}{dz}=-p\,\hat\rho\,g(w),\qquad\text{so}\qquad \frac{dp}{dw}=\frac{\delta(w)}{\hat\rho\,g(w)}-1 .$$

Every point $(0,w^*)$ is an equilibrium. **Theorem.** Suppose $g(w)=w\,G(w)$ with $G$ bounded, $g$ strictly increasing and $\delta$ strictly decreasing on $[0,1]$. Then solutions with positive initial data stay positive and bounded, and the reduced system has a positive heteroclinic orbit from $(p,w)=(0,1)$ to some $(0,w^*)$ with $w^*\in[0,1)$. Behind the front a fraction $w^*$ of space stays free and $1-w^*$ is filled by quiescent cells.

## Depends on

- [Every Fisher–KPP front speed is at least the minimal speed](../../fisher-kpp-travelling-waves/two-mul-sqrt-le-of-is-front.md)

## Expansion

Positivity follows from writing each equation as $x'=x\,f$ with bounded $f$; boundedness from $d(p+w)/dz=-\delta(w)\le0$. Along the orbit $d^2p/dw^2=(\delta'g-\delta g')/(\hat\rho g^2)<0$, and $dp/dw=-1$ at $w=1$, so the orbit leaving $(0,1)$ stays below the line $p=1-w$. Monotonicity of $g,\delta$ gives a unique $w^\dagger$ where $dp/dw=0$; $w$ decreases to a limit $w^*$, and $w^*<w^\dagger$ because the system has no positive equilibrium. Below $w^\dagger$ the growth factor $\hat\rho g(w)-\delta(w)$ is negative, so $p\to0$ exponentially. The cross-diffusion terms drop out of the reduced system: they only set the speed through the linearised leading edge and the length scale $\sqrt{D/k}$.

## Sources

- L. Han, S. Eikenberry, C. He, L. Johnson, M. C. Preul, E. J. Kostelich, Y. Kuang, "Patient-specific parameter estimates of glioblastoma multiforme growth dynamics from a model with explicit birth and death rates", *Mathematical Biosciences and Engineering* (2019), Eqs. (2.1)–(2.9), Section 2.2, Appendix Lemma 1 and Theorem 1, <https://doi.org/10.3934/mbe.2019265>, PMCID PMC7304543.
