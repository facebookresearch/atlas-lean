# Separatrix criterion for large-amplitude oscillations near a singular Hopf bifurcation

**Ecological model.** One prey $x$ and two competing predators $y,z$ with slow predator dynamics ($0<\zeta\ll1$), in slow time $s$:

$$\zeta\dot x=x\Big(1-x-\frac{y}{\beta_1+x}-\frac{z}{\beta_2+x}\Big),\quad \dot y=y\Big(\frac{x}{\beta_1+x}-c-\alpha_{12}z\Big),\quad \dot z=z\Big(\frac{x}{\beta_2+x}-d-\alpha_{21}y-hz\Big),$$

with $0<\beta_1,\beta_2,c,d,\alpha_{12},\alpha_{21}<1$ and intraspecific predator competition $h>0$ as bifurcation parameter. Near a folded saddle-node of type II, where the coexistence equilibrium crosses the fold curve of the nontrivial prey-nullcline surface (where the fast prey equation loses normal hyperbolicity), a singular Hopf bifurcation produces long chaotic mixed-mode transients that end either in a large excursion or on a stable periodic orbit, with indistinguishable local time series.

**Normal form.** Under non-degeneracy conditions (P1)–(P6) at the type II folded saddle-node point, with $\delta=\sqrt\zeta/\omega=O(\sqrt\zeta)$ and $\tau=s/\delta$, the system is locally equivalent to

$$u'=v+\tfrac12u^2+\delta\big(\alpha u+F_{13}uw+\tfrac16F_{111}u^3\big)+O(\delta^2),\quad v'=-u+O(\delta^2),\quad w'=\delta\big(H_3w+\tfrac12H_{11}u^2\big)+O(\delta^2),$$

where $\alpha=\alpha(h)$ unfolds the Hopf bifurcation and $F_{13},F_{111},H_3,H_{11}$ are explicit in the model parameters. Freezing the slow variable $w=\lambda$ gives the planar fast system $u'=\delta(\alpha+F_{13}\lambda)u+v+\tfrac12u^2+\tfrac{\delta}{6}F_{111}u^3$, $v'=-u$, with a Hopf bifurcation at $\lambda_H(\alpha)=-\alpha/F_{13}+O(\delta)$, supercritical when $F_{111}<0$.

**Type I and Type II oscillations.** A planar orbit starting at $(0,v_\lambda)$, $v_\lambda>0$, is a graph $v=q(u)$ until $u'$ first vanishes. It is *Type I* (small-amplitude) if $q'$ is monotone there and *Type II* (large-amplitude) if $q'$ has two local extrema. The *critical threshold*

$$v^\star_\alpha(\lambda)=\sup\{v_\lambda>0:\ q''<0\ \text{on the first arc}\}$$

defines the separatrix $S_{\alpha,\lambda}$ between the two types.

**Lemmas.** Assume $F_{13}>0$, $F_{111}<0$, $\alpha>0$, $\lambda_H(\alpha)<\lambda\le0$ and $\delta>0$ small. Then (i) $S_{\alpha,\lambda}$ is tangent to the inflection curve $g(u,v,\lambda)=0$ at $u^*_0=-1/(\delta F_{111})$; (ii) $v^\star_\alpha(\lambda)$ decreases monotonically in $\lambda$ (and in $\alpha$).

**Theorem (early-warning criterion).** Assume $F_{13}>0$, $F_{111}<0$, $H_3<0$, $H_{11}<0$. For every $\alpha\in(\alpha_c,\alpha_s]$ and $\delta>0$ sufficiently small, a solution of the three-dimensional normal form with $0<|u(0)|,|v(0)|\ll1$ and $w(0)>\lambda_c(\alpha)$ makes a Type II (large-amplitude) oscillation **if and only if** at some time $\tau^+>0$ it crosses the half-plane $\{u=0\}$ with

$$v(\tau^+)>v^\star_\alpha\big(w(\tau^+)\big)\quad\text{and}\quad w(\tau^+)>\lambda_c(\alpha).$$

Here $\alpha_c$ is the largest unfolding value for which planar orbits never meet the singular canard $\Gamma^0$, $\alpha_s$ bounds the range where the Hopf cycle stays the unique attractor, and $\lambda_c(\alpha)$ is the level at which the separatrix closes into a periodic orbit.

## Expansion

At $\delta=0$ the layer problem $u'=v+u^2/2$, $v'=-u$ is integrable with first integral $(u^2+2v-2)e^v=-k$; the level $k=0$ is the singular canard separating closed orbits from orbits that escape. For small $\delta$ the slowly drifting $w$ acts as a moving parameter. Each helical turn of a trajectory crosses $\{u=0\}$; by Lemma (ii), while it descends with Type I turns the threshold rises, so the first return map is monotone, and a large excursion occurs exactly when a crossing height exceeds the threshold at the current slow level. The criterion turns the separatrix into a computable early-warning signal of a regime shift, using normal-form variables.

## Sources

- S. Sadhu, *Analysis of long-term transients and detection of early warning signs of major population changes in a two-timescale ecosystem*, arXiv:2105.09411 (2021), Section 2 (model), Theorem 3.1 (normal form), Section 3.3, Lemma 3.1, Lemma 3.2 and Theorem 3.3. <https://doi.org/10.48550/arXiv.2105.09411>
