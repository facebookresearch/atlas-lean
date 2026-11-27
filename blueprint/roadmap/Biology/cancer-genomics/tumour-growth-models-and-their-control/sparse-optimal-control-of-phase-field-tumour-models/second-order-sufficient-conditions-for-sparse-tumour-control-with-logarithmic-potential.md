# Second-order sufficient conditions for sparse optimal control of a phase-field tumour model with logarithmic potential

**State system.** On a smooth bounded $\Omega\subset\mathbb R^3$, $Q=\Omega\times(0,T)$, with $\alpha,\beta>0$, the chemical potential $\mu$, tumour fraction $\varphi$ and nutrient $\sigma$ solve the viscous Cahn–Hilliard–reaction–diffusion system

$$\begin{aligned} \alpha\partial_t\mu+\partial_t\varphi-\Delta\mu&=P(\varphi)\big(\sigma+\chi(1-\varphi)-\mu\big)-h(x,t)\,u_1,\\ \beta\partial_t\varphi-\Delta\varphi+F_1'(\varphi)+F_2'(\varphi)&=\mu+\chi\sigma,\\ \partial_t\sigma-\Delta\sigma&=-\chi\Delta\varphi-P(\varphi)\big(\sigma+\chi(1-\varphi)-\mu\big)+u_2, \end{aligned}$$

with homogeneous Neumann conditions, where $F_1$ is the singular logarithmic part of the double-well potential (e.g. $F_1(r)=(1+r)\log(1+r)+(1-r)\log(1-r)$ on $(-1,1)$), $F_2$ is smooth, $u_1$ is a cytotoxic drug acting through $h$ and $u_2$ a nutrient supply. For controls in the box $\mathcal U_{ad}=\{\underline u_i\le u_i\le\overline u_i\}$ the system is well posed with strong solutions and $\varphi$ stays uniformly separated from $\pm1$, so the control-to-state map $\mathcal S$ is twice Fréchet differentiable.

**Control problem.** Minimize

$$\widehat J(\mathbf u)=\frac{b_1}{2}\int_Q|\varphi-\widehat\varphi_Q|^2+\frac{b_2}{2}\int_\Omega|\varphi(T)-\widehat\varphi_\Omega|^2+\frac{b_3}{2}\int_Q|\mathbf u|^2+\kappa\int_Q\big(|u_1|+|u_2|\big)$$

over $\mathcal U_{ad}$, with $\kappa>0$ and $\underline u_i<0<\overline u_i$. Write $\widehat J_1$ for the smooth part.

**Theorem (first order and full sparsity).** If $\mathbf u^*$ is locally optimal with adjoint state $(p^*,q^*,r^*)$, there is $\boldsymbol\lambda^*\in\partial g(\mathbf u^*)$, $g(\mathbf u)=\int_Q(|u_1|+|u_2|)$, with

$$\int_Q\big(-hp^*+\kappa\lambda_1^*+b_3u_1^*\big)(u_1-u_1^*)+\int_Q\big(r^*+\kappa\lambda_2^*+b_3u_2^*\big)(u_2-u_2^*)\ge0\qquad\forall\,\mathbf u\in\mathcal U_{ad},$$

and, for a.e. $(x,t)\in Q$,

$$u_1^*(x,t)=0\iff|h(x,t)p^*(x,t)|\le\kappa,\qquad u_2^*(x,t)=0\iff|r^*(x,t)|\le\kappa .$$

**Theorem (second-order sufficient condition).** Let $\mathbf u^*$ satisfy the first-order conditions and define the critical cone

$$C_{\mathbf u^*}=\big\{\mathbf v\in C(\mathbf u^*):\ D\widehat J_1(\mathbf u^*)[\mathbf v]+\kappa\,g'(\mathbf u^*;\mathbf v)=0\big\},$$

where $C(\mathbf u^*)$ is the cone of feasible directions ($v_i\ge0$ where $u_i^*=\underline u_i$, $v_i\le0$ where $u_i^*=\overline u_i$) and $g'$ is the directional derivative of $g$. If

$$\widehat J_1''(\mathbf u^*)[\mathbf v,\mathbf v]>0\qquad\forall\,\mathbf v\in C_{\mathbf u^*}\setminus\{\mathbf 0\},$$

then there are $\varepsilon,\tau>0$ with the quadratic growth

$$\widehat J(\mathbf u)\ge\widehat J(\mathbf u^*)+\tau\|\mathbf u-\mathbf u^*\|_{L^2(Q)^2}^2\qquad\text{for all }\mathbf u\in\mathcal U_{ad},\ \|\mathbf u-\mathbf u^*\|_{L^2(Q)^2}<\varepsilon,$$

so $\mathbf u^*$ is a strict local minimizer in $L^2(Q)^2$.

## Expansion

The critical cone is small: pointwise, $v_1$ must vanish wherever $|-hp^*+b_3u_1^*|\neq\kappa$, and it carries sign restrictions at the bounds and where the sparsity switch is active; similarly for $v_2$ with $r^*$. The nonsmooth $L^1$ term contributes only through its convexity, so positivity of the second derivative of the smooth part on this cone suffices. The proof argues by contradiction with a sequence violating quadratic growth, normalizes the differences, and passes to the limit using that $\widehat J_1'$ and $\widehat J_1''$ are continuous along strongly convergent controls and weakly convergent directions; the uniform separation of $\varphi$ from $\pm1$ keeps the logarithmic potential and its derivatives bounded, which is what makes the second-order analysis possible for a singular potential.

## Sources

- Jürgen Sprekels, Fredi Tröltzsch, "Second-Order Sufficient Conditions in the Sparse Optimal Control of a Phase Field Tumor Growth Model with Logarithmic Potential", ESAIM: Control, Optimisation and Calculus of Variations 30 (2024), 13, <https://doi.org/10.1051/cocv/2023084>. Published version of arXiv:2306.06389, cited next; locators there refer to the arXiv version.
- Jürgen Sprekels, Fredi Tröltzsch, "Second-order sufficient conditions in the sparse optimal control of a phase field tumor growth model with logarithmic potential", arXiv:2306.06389 (2023): problem (CP), Theorem on strong solutions (Section 2), necessary optimality condition and full-sparsity theorem (Sections 3.1–3.2), critical cone and second-order sufficient condition (Section 3.3), Corollary 4.1 and Lemma 4.2. <https://doi.org/10.48550/arXiv.2306.06389>
