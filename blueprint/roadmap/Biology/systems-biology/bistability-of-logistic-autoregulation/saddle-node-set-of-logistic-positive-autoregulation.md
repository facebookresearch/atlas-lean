# Saddle-node set of logistic positive autoregulation

**Model.** mRNA $m$ and protein $x$ of a self-activating gene obey

$$\dot m=k_mf(x)-k_{dm}m,\qquad \dot x=k_pm-k_{dp}x,\qquad f(x)=\frac1{1+e^{-\lambda(x-\theta)}},$$

with steepness $\lambda>0$ and threshold $\theta>0$. Steady states solve $x=\alpha f(x)$ with $\alpha=k_mk_p/(k_{dm}k_{dp})$. Unlike a Hill kernel, $f(0)>0$ gives basal expression.

**Theorem.**

- (i) Saddle-node bifurcations occur exactly at the pairs $(\alpha,x)$ with $z=\lambda(x-\theta)$ solving

$$e^z-z=\lambda\theta-1,\qquad \alpha_{\rm crit}(z)=\frac{(1+e^z)(1+e^{-z})}{\lambda}=\frac{2+e^z+e^{-z}}\lambda .$$

- (ii) This equation has no real root if $\lambda\theta<2$, the double root $z=0$ if $\lambda\theta=2$ (a cusp at $\alpha=2$), and exactly two roots $z_-<0<z_+$ if $\lambda\theta>2$. Bistability holds exactly for $\alpha_{\rm lower}=\alpha_{\rm crit}(z_+)<\alpha<\alpha_{\rm crit}(z_-)=\alpha_{\rm upper}$.
- (iii) As $\lambda\to\infty$ with $\theta$ fixed, $\alpha_{\rm lower}\to\theta$ and $\alpha_{\rm upper}\sim e^{\lambda\theta-1}/\lambda\to\infty$, so the bistable range tends to $(\theta,\infty)$, the range of the step-function (Boolean) limit.

**Global behaviour.** The rectangle $[0,k_m/k_{dm}]\times[0,\alpha]$ is forward invariant and absorbs every trajectory; the divergence of the vector field is $-(k_{dm}+k_{dp})<0$, so there are no closed orbits and every trajectory converges to an equilibrium, the outer two being stable in the bistable range. For networks built from products of logistic kernels the right-hand side is globally Lipschitz with an explicit constant, so one-step integrators converge at full order with explicit error constants.

## Depends on

- [Genetic toggle switch](../genetic-toggle-switch/README.md)

## Expansion

A saddle-node is a tangency of the line $x/\alpha$ with $f$: $x=\alpha f(x)$ and $1=\alpha f'(x)=\alpha\lambda f(1-f)$. Dividing gives $1=\lambda x(1-f(x))=\lambda x/(1+e^z)$, i.e. $\lambda\theta+z=1+e^z$, and then $\alpha=x/f(x)=(1+e^z)(1+e^{-z})/\lambda$. The function $e^z-z$ has minimum $1$ at $z=0$, which gives the root count, and for large $\lambda\theta$ the roots satisfy $e^{z_+}\approx\lambda\theta$ and $z_-\approx1-\lambda\theta$, giving the asymptotics. Bendixson's criterion rules out cycles in the planar system.

## Sources

- I. Belgacem, "Numerical Reliability of Logistic Gene Regulatory Network Models: Preventing Expression Shutdown and Robust Integration", arXiv:2605.01056 (2026), model (autoreg\_logistic), Theorem 3.1, Corollary 3.2, Proposition 4.1, <https://doi.org/10.48550/arXiv.2605.01056>.
