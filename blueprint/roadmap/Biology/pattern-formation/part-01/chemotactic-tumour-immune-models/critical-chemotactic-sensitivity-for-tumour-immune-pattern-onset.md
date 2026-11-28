# Critical chemotactic sensitivity for tumour–immune pattern onset

**Setting.** For the chemotactic tumour–immune system

$$
\begin{aligned}
u_t&=d_1\Delta u+u(1-u-v),\\
v_t&=d_2\Delta v-\xi\nabla\cdot(v\nabla w)+\sigma_0+\sigma_1\frac{w}{1+w}-\delta v-\beta uv,\\
w_t&=d_3\Delta w+\alpha u+\gamma uv-\ell w,
\end{aligned}
$$

on a bounded smooth domain with no-flux conditions, let $(u^*,v^*,w^*)$ be a homogeneous coexistence equilibrium and let $0=\mu_0<\mu_1\le\mu_2\le\cdots$ be the Neumann eigenvalues of $-\Delta$. Linearizing the physical no-flux conditions at a homogeneous state gives exactly componentwise Neumann conditions, so perturbations decompose into Neumann modes; mode $k$ grows like $e^{\lambda t}$ with $\lambda$ a root of a cubic $\lambda^3+a_1(k)\lambda^2+a_2(k;\xi)\lambda+a_3(k;\xi)=0$. Write $\omega_k(\xi)$ for the largest real part of its roots.

**Proposition.** Assume the equilibrium is stable to the homogeneous mode $k=0$. Then for every $k\ge1$:

1. $a_1(k)>0$; $a_2(k;\xi)$ is affine and strictly decreasing in $\xi$ with slope $-v^*\mu_kt<0$, for a positive constant $t$ fixed by the equilibrium; $a_3(k;\xi)$ is affine in $\xi$ with slope $-v^*\mu_k(A_kt-ps)$, where $A_k$ and $s,p$ are fixed by the mode and the equilibrium, so it is decreasing if and only if $A_kt>ps$. (The source's Proposition 6.2(i) prints "both strictly decreasing", against its own slope formula; its Remark 6.3 notes $A_kt-ps<0$ throughout the unstable band for its Table 3, where $a_3$ increases in $\xi$.) Hence the Hurwitz determinant $H_k(\xi)=a_1a_2-a_3$ is affine in $\xi$, and $\xi\mapsto\omega_k(\xi)$ is continuous and eventually positive.
2. Since $\omega_k(0)<0$ for all $k$ and $\omega_k(\xi)\to+\infty$ as $\xi\to\infty$ whenever $\mu_k>0$, the critical sensitivity

$$
\xi_c=\inf\Big\{\xi\ge0:\max_{k\ge1}\omega_k(\xi)\ge0\Big\}
$$

lies in $(0,\infty)$ and is attained at a finite mode $k^*\ge1$.
3. At $\xi=\xi_c$ exactly one of the following holds for the critical mode: (a) $a_3(k^*;\xi_c)=0$ with $a_1a_2-a_3>0$, a simple real eigenvalue crossing zero (stationary, Turing-type onset); or (b) $a_1a_2-a_3=0$ with $a_3>0$, a complex pair crossing the imaginary axis at $\pm i\sqrt{a_2}$ (oscillatory, Hopf-type onset).

## Expansion

The chemotactic flux enters the linearization only through $-\xi v^*\mu_k\tilde w$ in the $v$-equation, so $\xi$ appears linearly in the mode matrix and hence affinely in the Routh–Hurwitz coefficients. By the Routh–Hurwitz criterion a cubic with $a_1>0$ is stable iff $a_3>0$ and $a_1a_2>a_3$; increasing $\xi$ drives one of these two quantities to zero first, which decides whether the instability is stationary or oscillatory. The onset must therefore be located from $\omega_k$ itself rather than from the constant-term threshold $a_3=0$ alone; for the paper's calibrated parameters the onset is oscillatory, at mode $k^*=5$.

## Depends on

- [Tumour-free threshold of a chemotactic tumour–immune model](tumour-free-threshold-of-a-chemotactic-tumour-immune-model.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Sources

- Zonghao Liu, Jiguang Yu, Lei Su, Louis Shuo Wang, "Computational Oncology of Chemotaxis-Driven Tumour--Immune Spatial Patterning and Stability", arXiv:2607.03813: Section 6: Lemma 6.1 (linearized flux reduces to Neumann), Proposition 6.2 (existence of a critical sensitivity and nature of the onset), Remark 6.3; Appendix B (Routh–Hurwitz details). <https://doi.org/10.48550/arXiv.2607.03813>
