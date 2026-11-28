# Tumour-free threshold of a chemotactic tumour–immune model

**Model.** On a bounded smooth domain $\Omega\subset\mathbb{R}^d$ with no-flux boundary conditions, let $u$ be tumour density, $v$ immune effector density and $w$ chemokine concentration, in nondimensional form

$$
\begin{aligned}
u_t&=d_1\Delta u+u(1-u-v),\\
v_t&=d_2\Delta v-\xi\nabla\cdot(v\nabla w)+\sigma_0+\sigma_1\frac{w}{1+w}-\delta v-\beta uv,\\
w_t&=d_3\Delta w+\alpha u+\gamma uv-\ell w,
\end{aligned}
$$

with positive diffusivities $d_i$, chemotactic sensitivity $\xi\ge0$, baseline immune supply $\sigma_0>0$, chemokine-recruited supply $\sigma_1\ge0$, immune loss $\delta>0$, inactivation $\beta\ge0$, chemokine production $\alpha,\gamma\ge0$ and decay $\ell>0$.

**Theorem (tumour-free threshold).** The tumour-free equilibrium $E_0=(0,\sigma_0/\delta,0)$ is linearly stable if $\sigma_0>\delta$, linearly unstable if $\sigma_0<\delta$, and non-hyperbolic if $\sigma_0=\delta$. The chemotactic sensitivity $\xi$ does not enter this threshold.

**Proposition (coexistence equilibria).** Every spatially homogeneous coexistence equilibrium has $v^*=1-u^*$ and $w^*=u^*[\alpha+\gamma(1-u^*)]/\ell$, with $u^*\in(0,1)$ a zero of

$$
F(u)=\sigma_0+\sigma_1\frac{w(u)}{1+w(u)}-(\delta+\beta u)(1-u),\qquad w(u)=\frac{u[\alpha+\gamma(1-u)]}{\ell}.
$$

If $\sigma_0<\delta$ and $F(1)>0$, at least one interior coexistence equilibrium exists.

**Well-posedness.** For nonnegative compatible data in $C^{2+\theta}(\bar\Omega)$ there is a unique nonnegative classical solution on a maximal interval $[0,T_{\max})$, with blow-up of the $L^\infty$ norm if $T_{\max}<\infty$; on that interval $0\le u\le\max\{1,\|u_0\|_\infty\}$, and the masses $\int_\Omega v$ and $\int_\Omega w$ stay bounded.

## Expansion

At $E_0$ the tumour equation linearizes to $\tilde u_t=d_1\Delta\tilde u+(1-\sigma_0/\delta)\tilde u$, decoupled from the others, and the chemotactic flux $-\xi\nabla\cdot(v\nabla w)$ linearizes to $-\xi v_0\Delta\tilde w$, which only affects the $(v,w)$ block whose eigenvalues are negative; hence the threshold $\sigma_0/\delta=1$. In dimensional units $\sigma_0/\delta$ is the ratio of the baseline immune kill rate to the tumour proliferation rate. $F(0)=\sigma_0-\delta<0<F(1)$ gives an interior root by the intermediate value theorem. Global boundedness in arbitrary dimension is not claimed: the bounds above control only $u$ in $L^\infty$ and $v,w$ in $L^1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- Zonghao Liu, Jiguang Yu, Lei Su, Louis Shuo Wang, "Computational Oncology of Chemotaxis-Driven Tumour--Immune Spatial Patterning and Stability", arXiv:2607.03813: Theorem 4.1, Propositions 4.2–4.3 (well-posedness and bounds), Theorem 5.1 (tumour-free threshold), Proposition 5.3 (coexistence equilibria). <https://doi.org/10.48550/arXiv.2607.03813>
