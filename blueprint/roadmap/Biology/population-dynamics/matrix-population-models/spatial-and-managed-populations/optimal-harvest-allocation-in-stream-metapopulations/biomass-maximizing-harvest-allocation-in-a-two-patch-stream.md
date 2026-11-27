# Biomass-maximizing harvest allocation in a two-patch stream

**Model.** Patch 1 is upstream, patch 2 downstream. With random dispersal rate $d>0$, downstream drift $q>0$, growth rate $r>0$, competition $c>0$ and total harvesting effort $H>0$ split as $\theta H$ upstream and $(1-\theta)H$ downstream, $\theta\in[0,1]$,

$$u_1'=u_1(r-\theta H-cu_1)-(d+q)u_1+du_2,\qquad u_2'=u_2(r-(1-\theta)H-cu_2)+(d+q)u_1-du_2 .$$

Assume the persistence condition $r>r_{\rm crit}=H\frac{d+q}{2d+q}$, so there is a globally stable positive equilibrium $(u_1^*(\theta),u_2^*(\theta))$, and let $\mathcal M(\theta)=u_1^*+u_2^*$ be the total biomass.

**Theorem.**

- If $r>2d+q+\tfrac H2$, then $\mathcal M(\theta)\le\mathcal M(0)$: biomass is maximized by harvesting only downstream.
- If $r_{\rm crit}\le r<2d+q+\tfrac H2$, then $\mathcal M(\theta)\le\mathcal M(1)$: biomass is maximized by harvesting only upstream.
- If $r=2d+q+\tfrac H2$, then $\mathcal M(\theta)\le\mathcal M(0)=\mathcal M(1)$.

**Shape of $\mathcal M$.** With

$$r_M=2d+q+\frac{\sqrt{d+q}}{\sqrt{d+q}-\sqrt d}\,H,\qquad r_m=2d+q-\frac{\sqrt d}{\sqrt{d+q}-\sqrt d}\,H,$$

$\mathcal M$ is strictly decreasing on $[0,1]$ if $r>r_M$, strictly increasing if $r<r_m$, and for $r_m\le r\le r_M$ it has a unique critical point, which is a minimum. For heterogeneous patches ($r_1,r_2,c_1=c_2$) the same trichotomy holds with $r$ replaced by $\frac{r_1\sqrt{d+q}-r_2\sqrt d}{\sqrt{d+q}-\sqrt d}$.

**Yield.** For the yield $\mathcal Y=\theta Hu_1^*+(1-\theta)Hu_2^*$: if $r>r_M$ and $q\ge 2H$ the yield is also maximized at $\theta=0$, so one strategy maximizes both objectives; if only $r>r_M$, the yield-maximizing split has $\theta^*<1/2$.

## Expansion

Summing the equilibrium equations eliminates the dispersal terms: $\sum_iu_i^*(r-h_i-cu_i^*)=0$. Implicit differentiation in $\theta$ gives $\mathcal M'(\theta)$ explicitly, and its sign is that of $g(\theta)-r$ for an increasing function $g$ with values between $r_m$ and $r_M$. Hence $\mathcal M$ is decreasing then increasing: it can have an interior minimum but never an interior maximum, so the biomass optimum is at $\theta=0$ or $\theta=1$, and comparing $\mathcal M(0)$ with $\mathcal M(1)$ reduces to the threshold $r=2d+q+H/2$.

## Sources

- T. D. Nguyen, Z. Shuai, T. Tang, A. Veprauskas, "Optimal Harvesting in Stream Networks: Maximizing Biomass and Yield", *Bulletin of Mathematical Biology* 88(6) (2026), 91, Section 3 (Lemma on persistence, Theorems 3.4, 3.5 and 3.11, Corollaries 3.6 and 3.12), <https://doi.org/10.1007/s11538-026-01658-8> (preprint arXiv:2602.05071).
