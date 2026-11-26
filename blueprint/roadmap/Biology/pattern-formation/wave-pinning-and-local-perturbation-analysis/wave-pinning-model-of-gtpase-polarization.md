# Wave-pinning model of GTPase polarization

Let $\Omega\subset\mathbb R^d$ be a bounded domain with outward normal $n$. Let $u(x,t)\ge0$ and $v(x,t)\ge0$ be the active (membrane-bound) and inactive (cytosolic) forms of a GTPase, nondimensionalised so that $v$ has diffusion coefficient $1$ and $u$ has diffusion coefficient $0<\delta\ll1$. The wave-pinning model is

$$\partial_t u=\delta\nabla^2u+f(u,v),\qquad \partial_t v=\nabla^2v-f(u,v),\qquad \partial_n u=\partial_n v=0\ \text{on }\partial\Omega,$$

$$f(u,v)=\Big(k+\gamma\frac{u^n}{1+u^n}\Big)v-\eta u,$$

with basal activation $k>0$, Hill-type positive feedback of strength $\gamma>0$ and order $n\ge2$, and inactivation rate $\eta>0$. The total amount

$$w=\int_\Omega(u+v)\,dx$$

is constant in time, so $w$ acts as a parameter. Conservation fixes only $\int_\Omega v\,dx=w-\int_\Omega u\,dx$, not the field $v(x,t)$: two inactive fields with the same integral can give different local reaction rates $f(u,v)$. In the reduced (well-mixed or local-perturbation) description, where the fast inactive pool is treated as spatially uniform, $v$ is eliminated as $v=\big(w-\int_\Omega u\,dx\big)/|\Omega|$.

A non-conservative extension adds degradation of active and synthesis of inactive GTPase, $\partial_tu=\delta\nabla^2u+f-\theta u$, $\partial_tv=\nabla^2v-f+\alpha$; it has the unique homogeneous equilibrium $u_*=\alpha/\theta$, $v_*=(\alpha+\eta u_*)/A(u_*)$ with $A(u)=k+\gamma u^n/(1+u^n)$.

## Expansion

Adding the two equations and integrating over $\Omega$ gives $\frac{d}{dt}\int_\Omega(u+v)\,dx=\int_{\partial\Omega}(\delta\partial_nu+\partial_nv)\,dS=0$ by the Neumann conditions. For suitable $(\gamma,w)$ the kinetics are bistable in $u$ at fixed $v$; a front between high and low $u$ travels, depletes the shared fast pool $v$, decelerates and stalls, leaving a stable polarized "pinned wave". In the non-conservative extension, local equilibria $u_L$ at the global $v_*$ satisfy $u_L/u_*=A(u_L)/A(u_*)$, which has no nontrivial solution for small $\gamma$.

## Sources

- Y. Liu, E. G. Rens, L. Edelstein-Keshet, "Spots, stripes, and spiral waves in models for static and motile cells: GTPase patterns in cells", J. Math. Biol. 82 (2021), article 28, Section 2.1, Equations (1) and (3), Section 3 (elimination of $v$ in the reduced system), Section 4.3 Equation (4), <https://doi.org/10.1007/s00285-021-01550-0>, PMCID PMC7929972.
