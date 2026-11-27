# Turing instability in the nonlocal membrane GTPase model

**Model.** GTPases cycle between an active membrane-bound form $u$, an inactive membrane-bound form $v$ and a cytosolic form $V$. If cytosolic diffusion is much faster than lateral membrane diffusion, $V$ is spatially uniform and fixed by mass conservation, giving the non-local reaction–diffusion system on a closed membrane surface $\Gamma$:

$$
\partial_tu=\Delta_\Gamma u+\gamma f(u,v),\qquad
\partial_tv=d\,\Delta_\Gamma v+\gamma\big(-f(u,v)+q(u+v,v,V[u+v])\big),
$$

$$
f(u,v)=\Big(a_1+(a_3-a_1)\frac{u}{a_2+u}\Big)v-a_4\frac{u}{a_5+u},\qquad
q=a_6V\,(1-(u+v))_+-a_{-6}v,\qquad V[u+v]=V_0-c\int_\Gamma(u+v).
$$

Here $f$ is activation (by GEF and by the GEF–GTPase–effector complex, Michaelis–Menten type) minus GAP-mediated deactivation, $q$ is attachment of cytosolic GTPase onto free membrane sites minus detachment, $d$ is the ratio of lateral diffusion of inactive to active GTPase, $\gamma$ scales system size, and $m=V_0/(c|\Gamma|)$.

**Theorem.**

1. *(Homogeneous steady state.)* If $a_2>a_5$, $4a_2a_4<a_3a_5\min\{m,1\}$, $4a_4a_5a_{-6}<V_0a_2a_3a_6$ and

$$
a_1<\min\Big\{\frac{a_3(a_2-a_5)}{2a_2},\ 2^{-8}\frac{a_3^2(a_2-a_5)^2}{a_2^2a_5}\big(\min\{m,1\}\big)^2\Big\}
$$

(the source's (3.26)), there is a spatially homogeneous steady state $(u_*,v_*)$ with $u,v\ge0$, $u+v\le\min\{1,m\}$.
2. *(Kinetic stability.)* If moreover $2a_4(a_2-a_5)<a_3a_5^2$ and $a_{-6}<a_6c|\Gamma||1-m|$, then $(u_*,v_*)$ is a stable equilibrium of the kinetic ODE and is of activator–substrate-depletion type ($u$ activator, $v$ substrate).
3. *(Turing instability.)* Under these conditions, if in addition (the source's (3.48)–(3.50))

$$
a_1<\min\Big\{\frac{\min\{1,m\}\,a_3}{2a_2(a_3^2+1)},\ \frac{\min\{1,m\}^2a_3(a_2-a_5)}{4a_2(a_2+1)^2(a_3^2+1)}\Big\},
$$

$$
d>\frac{2\big(a_3(a_3^2+2)+(a_2+1)(a_3^2+1)(a_6V_0+a_{-6})\big)(a_3^2+2)(a_5+1)^2}{\min\{1,m\}\,a_3^2a_4(a_2-a_5)(a_3^2+1)},
$$

$$
d>\frac{4(a_3^2+2)^2(a_5+1)^2\big(a_3^2a_4(a_2-a_5)\min\{1,m\}+4(a_3^2+2)a_6V_0(a_2+1)(a_5+1)^2\big)}{a_3^3(a_3^2+1)a_4^2(a_2-a_5)^2\min\{1,m\}^2},
$$

   then for some $\gamma>0$ the state $(u_*,v_*)$ is linearly unstable for the non-local reaction–diffusion system.
4. *(No instability for equal diffusion.)* If $d=1$ and $(u_*,v_*)$ is of activator–substrate-depletion type ($\partial_uf,\partial_vf>0$, $\partial_ug_0<0<\partial_vg_0$ with $g_0$ the homogeneous reaction term), then no Turing-type instability exists, despite the non-local coupling.

## Expansion

Linearizing about $(u_*,v_*)$, a spatial Laplace–Beltrami mode with eigenvalue $-k^2$ only sees the local Jacobian, because the non-local term $V[u+v]$ is a mean and vanishes on non-constant modes; the homogeneous mode sees the extra term $-c|\Gamma|$ through $q_0$. The usual Turing inequalities then require the inhibitor-like inactive form to diffuse substantially faster ($d\gg1$), and $\gamma$ large enough for an unstable wavenumber to fit on $\Gamma$. The condition $a_2>a_5$ says the activating complex binds active GTPase more strongly than GAP does, and $a_1\ll a_3$ says complex-mediated activation dominates basal activation. For $d=1$ the model is a mass-conserving activator–substrate system with equal diffusion, for which the mode-$k$ stability matrix stays Hurwitz for all $k$. Membrane–cytosol coupling therefore supports polarity-forming Turing patterns, but only when inactive GTPase diffuses laterally much faster than active GTPase.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Sources

- Andreas Rätz, Matthias Röger, "Turing instabilities in a mathematical model for signaling networks", arXiv:1107.1594 (2011), Section 2 (model and reduction), Section 3: Propositions 3.1–3.2, Lemma 3.3, Theorem 3.4, Remark 3.5; Section 4: Theorem 4.1, <https://doi.org/10.48550/arXiv.1107.1594>.
