# Only constant bounded stationary states for the nonlocal Fisher–KPP equation with small nonlocality

The **nonlocal Fisher–KPP equation** $u_t=\Delta u+\mu u(1-\phi*u)$ on $\mathbb R^d$ models a population whose per-capita growth is limited by competition with neighbors weighted by a kernel $\phi$. Its stationary equation is

$$0=\Delta u+\mu u(1-\phi*u),\qquad x\in\mathbb R^d.$$

After the rescaling $\tilde x=\sigma x$ with $\mu=\sigma^2$, this becomes $0=\Delta u+u(1-\phi_\sigma*u)$, where $\phi_\sigma(x)=\sigma^{-d}\phi(x/\sigma)\to\delta$ as $\sigma\to0$. The constants $u\equiv0$ and $u\equiv1$ always solve it when $\int\phi=1$.

**Theorem.** Assume (A): $\phi\in L^1(\mathbb R^d)$, $\phi\ge0$, $\int_{\mathbb R^d}\phi=1$. For every $K>1$ there is $\sigma_0>0$ (equivalently $\mu_0>0$) such that, for $\sigma\in[0,\sigma_0]$ (respectively $\mu\in(0,\mu_0]$), the only nonnegative bounded classical solutions $u\in C^2_b(\mathbb R^d)$ with $\|u\|_{C^2_b}\le K$ of the stationary nonlocal Fisher–KPP equation are $u\equiv0$ and $u\equiv1$.

For $d=1$ and kernels with $\phi(0)>0$, $\nabla\phi\in C_b$ and a finite second moment, Berestycki–Nadin–Perthame–Ryzhik had shown the same conclusion without the a priori $C^2_b$ bound. The theorem extends it to all dimensions under integrability alone, at the cost of the bound $K$, on which $\sigma_0$ depends.

## Expansion

At $\sigma=0$ the equation is the local problem $\Delta u+u(1-u)=0$. Its only bounded nonnegative solutions on $\mathbb R^d$ are $0$ and $1$; the Kong–Shen / Berestycki–Hamel–Roques theorem (strictly decreasing per-capita growth rate $f(u)/u$) gives uniqueness of the positive solution with $\inf u>0$. The proof treats small $\sigma$ as a perturbation of this local problem. In polynomially weighted Sobolev spaces with weights $(1+|x|^2)^{-l}$, $l>\tfrac12$, the linearization at $u\equiv1$, $\mathcal L_1=\Delta-1$, is invertible with bounded inverse, so the implicit function theorem keeps $u\equiv1$ isolated. Near $u\equiv0$ the linearization $\Delta+1$ has only purely oscillatory bounded kernel elements (Hörmander's description of exponential solutions), and these are incompatible with nonnegativity, which excludes a branch bifurcating from $0$. For large nonlocality, nonconstant stationary patterns can appear, so the smallness of $\sigma$ is essential.

## Sources

- Franz Achleitner, Christian Kuehn, "On Bounded Positive Stationary Solutions for a Nonlocal Fisher-KPP Equation", arXiv:1307.3480 (2013), equations (1.2)–(1.4), Theorem 1.1 (after Berestycki et al.), Theorems 2.1–2.2, Propositions 4.2 and 5.2–5.6, <https://doi.org/10.48550/arXiv.1307.3480>.
