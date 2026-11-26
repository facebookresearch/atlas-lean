# Reactivity conditions for diffusion–chemotaxis-driven instability

**Model.** Consider the two-species reaction–diffusion–chemotaxis system

$$
\partial_t u=D_u\Delta u-\beta\,\nabla\cdot(u\nabla v)+f(u,v),\qquad \partial_t v=D_v\Delta v+g(u,v),
$$

with $D_u,D_v>0$ and chemotactic sensitivity $\beta\in\mathbb R$. Let $(u^*,v^*)$ be a homogeneous equilibrium, $f(u^*,v^*)=g(u^*,v^*)=0$, with kinetic Jacobian $J^*=\begin{pmatrix}f_u&f_v\\ g_u&g_v\end{pmatrix}$ asymptotically stable: $f_u+g_v<0$ and $\det J^*=f_ug_v-f_vg_u>0$. For a Fourier mode of wavenumber $k$ the linearization is $\dot{\tilde{\mathbf w}}=J_k\tilde{\mathbf w}$ with

$$
J_k=J^*-k^2D-k^2C,\qquad D=\begin{pmatrix}D_u&0\\0&D_v\end{pmatrix},\quad C=\begin{pmatrix}0&-\beta u^*\\0&0\end{pmatrix}.
$$

*Diffusion–chemotaxis-driven instability* means $\alpha(J_k)=\max\operatorname{Re}\lambda(J_k)>0$ for some $k\ne0$; it occurs exactly when

$$
D_ug_v+D_vf_u+\beta g_uu^*>2\sqrt{D_uD_v\det J^*},
$$

which for $\beta=0$ is the classical Turing condition. The *reactivity* (numerical abscissa) of a real matrix $A$ is $r(A)=\lambda_{\max}(H(A))$ with $H(A)=\tfrac12(A+A^{\mathsf T})$, the maximal initial growth rate of $\|e^{tA}\mathbf w_0\|$; $A$ is *reactive* if $r(A)>0$. Always $\alpha(A)\le r(A)$.

**Proposition 1.** Diffusion–chemotaxis-driven instability requires $J_k$ to be reactive for some $k\ne0$.

**Proposition 2 (Neubert–Caswell–Murray).** Turing (diffusion-driven, $\beta=0$) instability requires $J^*$ to be reactive.

**Proposition 3.** Diffusion–chemotaxis-driven instability requires $J^*-k^2C$ to be reactive for some $k\ne0$. If moreover

$$
|\beta|\,u^*\le2\sqrt{D_uD_v},
$$

then reactivity of $J^*$ itself is necessary for diffusion–chemotaxis-driven instability.

**Consequence.** When $|\beta|u^*>2\sqrt{D_uD_v}$ the requirement that $J^*$ be reactive drops out: sufficiently strong chemotaxis can destabilize an equilibrium whose kinetics are stable and non-reactive (for a stable $J^*$, non-reactivity reads $f_ug_v>(f_v+g_u)^2/4$, forcing $f_u,g_v<0$, so diffusion alone cannot destabilize it).

## Expansion

Proposition 1 is $\alpha\le r$. For Proposition 2, $H(J_k)=H(J^*)-k^2D$ with $D$ positive definite, so Weyl's inequality gives $r(J_k)\le r(J^*)$. With chemotaxis, $H(J_k)=H(J^*-k^2C)-k^2D$ gives $r(J_k)\le r(J^*-k^2C)-k^2\min\{D_u,D_v\}$, the first claim of Proposition 3. Writing instead $H(J_k)=H(J^*)-k^2(D+H(C))$, the matrix $D+H(C)=\begin{pmatrix}D_u&-\beta u^*/2\\-\beta u^*/2&D_v\end{pmatrix}$ is positive semidefinite exactly when $|\beta|u^*\le2\sqrt{D_uD_v}$, and then $r(J_k)\le r(J^*)$. The asymmetric chemotactic transport matrix $C$ contributes an indefinite Hermitian part, which is what breaks the classical link between transient amplification and Turing patterns.

## Sources

- Angela Monti. *Pattern formation: reactivity is not necessary for chemotaxis-driven instabilities* (2026), Sections 2–3 and 5.2: Definition 1, Propositions 1–3 and Theorem 2. <https://doi.org/10.48550/arXiv.2608.03685>
