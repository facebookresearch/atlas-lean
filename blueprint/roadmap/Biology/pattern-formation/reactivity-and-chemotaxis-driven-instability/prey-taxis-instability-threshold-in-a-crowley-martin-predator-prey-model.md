# Prey-taxis instability threshold in a Crowley–Martin predator–prey model

**Model.** Predators $u$ and prey $v$ on $\Omega\subset\mathbb R^2$ with homogeneous Neumann boundary conditions satisfy

$$
\partial_tu=D_u\Delta u-\beta\nabla\cdot(u\nabla v)+\gamma\Big(-du+\frac{cuv}{(1+av)(1+bu)}\Big),\qquad
\partial_tv=D_v\Delta v+\gamma\Big(v(1-v)-\frac{uv}{(1+av)(1+bu)}\Big),
$$

with diffusion coefficients $D_u,D_v>0$, prey-taxis sensitivity $\beta\in\mathbb R$, predator mortality $d>0$, conversion efficiency $c>0$, handling parameter $a>0$, interference parameter $b>0$ and scale $\gamma>0$. Write $f$ and $g$ for the two reaction terms (including the factor $\gamma$).

**Theorem.** Let $P_e=(u^*,v^*)$ be a positive homogeneous equilibrium whose kinetic Jacobian $J^*$ is asymptotically stable, $\operatorname{tr}J^*<0$ and $\det J^*=f_ug_v-f_vg_u>0$. Then $P_e$ undergoes diffusion–chemotaxis-driven instability whenever

$$
\beta<\beta^*:=\frac{2\sqrt{D_uD_v\,(f_ug_v-f_vg_u)}-(D_ug_v+D_vf_u)}{g_u\,u^*},
$$

all partial derivatives being evaluated at $P_e$.

## Expansion

This is the general instability condition $D_ug_v+D_vf_u+\beta g_uu^*>2\sqrt{D_uD_v\det J^*}$ from [the reactivity conditions for diffusion–chemotaxis instability](reactivity-conditions-for-diffusion-chemotaxis-instability.md), solved for $\beta$: here $g_u=-\gamma v^*/\big((1+av^*)(1+bu^*)^2\big)<0$, so dividing by $g_uu^*$ reverses the inequality. The example matters because parameters can be chosen with $J^*$ stable and non-reactive and $D_ug_v+D_vf_u<0$, so neither reactivity of the kinetics nor classical Turing instability is available; the patterns that appear once $\beta$ crosses $\beta^*$ are then produced by taxis alone, illustrating that reactivity is not necessary for chemotaxis-driven instability.

## Depends on

- [Reactivity conditions for diffusion–chemotaxis-driven instability](reactivity-conditions-for-diffusion-chemotaxis-instability.md)

## Sources

- Angela Monti. *Pattern formation: reactivity is not necessary for chemotaxis-driven instabilities* (2026), Sections 2–3 and 5.2: Definition 1, Propositions 1–3 and Theorem 2. <https://doi.org/10.48550/arXiv.2608.03685>
