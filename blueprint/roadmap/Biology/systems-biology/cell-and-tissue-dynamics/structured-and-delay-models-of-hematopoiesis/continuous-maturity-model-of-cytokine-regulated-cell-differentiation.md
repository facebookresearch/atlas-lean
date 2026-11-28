# Continuous-maturity model of cytokine-regulated cell differentiation

**Model.** Stem cells $w(t)$ self-renew at a net rate $\alpha(v)$ regulated by a cytokine signal $v(t)$; progenitors $u(x,t)$ mature continuously along a maturity variable $x\in[0,x^*]$ at speed $g(x,v)$ while proliferating at rate $p(x)$; fully mature cells leaving at $x^*$ feed the signal, which decays at rate $\mu$:

$$\frac{dw}{dt}=\alpha(v)w,\qquad \partial_tu+\partial_x\bigl[g(x,v)u\bigr]=p(x)u,\qquad u(0,t)=w(t),\qquad \frac{dv}{dt}=g(x^*,v)\,u(x^*,t)-\mu v .$$

Assume $g_x,g_{xx}$ bounded, $p\in C^1$, $\alpha$ continuous and decreasing with values in $[\alpha_\infty,\alpha(0)]$ and $\alpha_\infty<0$, and $0<g_-\le g\le g_+$. The model is the continuum limit of the multi-compartment hematopoiesis model with many intermediate compartments.

**Theorem.**
1. *(Well-posedness)* For $u_0\in C^1([0,x^*])$ there is a unique global solution, and $w,u,v$ are uniformly bounded.
2. *(Extinction)* If $\alpha(0)<0$, all solutions converge to zero exponentially.
3. *(Persistence)* If $\alpha(0)>0$ and $w(0)>0$, solutions with positive data stay bounded away from zero.
4. *(Steady state)* A strictly positive steady state exists iff $\alpha(0)>0$, and it is unique.

**Stability.** If $g=g(x)$ does not depend on $v$, linearization gives the delay-type characteristic equation

$$\lambda^2+\mu\lambda=\mu\bar v\,\alpha'(\bar v)\,e^{-\tau\lambda},\qquad \tau=\int_0^{x^*}\frac{ds}{g(s)},$$

and for $1<\tau\bar v|\alpha'(\bar v)|<\pi/2$ a Hopf bifurcation occurs at a single value $\mu_0>0$ of the decay rate; further bifurcations occur when $\tau\bar v|\alpha'(\bar v)|>2k\pi+\pi/2$. For the rates inherited from the discrete compartment model, $g(x,v)=2\bigl[1-\frac{a(x)}{1+kv}\bigr]p(x)$ with self-renewal fraction $a(0)=a_w>\frac12$, the steady state is locally linearly stable when $g$ is independent of $x$ and $p$ is constant; a non-decreasing proliferation rate can destabilize it.

## Expansion

Along characteristics, the progenitor density at maturity $x$ is the stem-cell output a transit time earlier, amplified by $\exp\int p$; so the feedback from mature cells to stem cells acts with a delay equal to the maturation time $\tau$. Instability therefore comes from delayed negative feedback, as in periodic hematological diseases, while the sign of $\alpha(0)$, the stem-cell growth rate without signal, decides extinction versus persistence.

## Sources

- Marie Doumic, Anna Marciniak-Czochra, Benoit Perthame and Jorge P. Zubelli, "A Structured Population Model of Cell Differentiation", arXiv:1012.0682 (2010), Section 1 (model and continuum limit, Proposition 1.1), Theorem 2.1, Corollaries 2.4 and 2.6, Theorems 3.1–3.2, Lemma 4.1 and Propositions 4.2–4.3, <https://doi.org/10.48550/arXiv.1012.0682>.
