# Global boundedness and exponential stabilization of the two-species degenerate Keller–Segel system

**Model.** Two cell populations $u,v$ on $\mathbb R^d$ ($d\ge3$) with porous-medium diffusion, logistic growth to carrying capacities $N_1,N_2$, and chemotaxis towards two chemicals $c,z$, each produced by both species:

$$
\begin{cases}
u_t=\Delta u^{m_1}-\nabla\cdot(u^{\sigma_1}\nabla c)+u(N_1-u),& -\Delta c+c=a_{11}u+a_{12}v,\\
v_t=\Delta v^{m_2}-\nabla\cdot(v^{\sigma_2}\nabla z)+v(N_2-v),& -\Delta z+z=a_{21}u+a_{22}v,
\end{cases}
$$

with $m_1,m_2>1$, $a_{ij}>0$, and nonnegative initial data $(u_0,v_0)\in L^1\cap L^\infty(\mathbb R^d)$. Weak solutions are understood in the distributional sense with $(u,v)\in L^\infty(0,T;L^1_+\cap L^\infty)$.

**Theorem.**

1. *(Global bounded weak solutions.)* If $\sigma_1,\sigma_2>1$ and

$$
\min\{m_1,m_2\}>1+\max\{\sigma_1,\sigma_2\}-\frac2d,
$$

   then for all such initial data there is a global weak solution that is uniformly bounded in time.
2. *(Exponential convergence.)* Let $\sigma_i=\frac{m_i+1}{2}$, assume $m_1>\frac{m_2-1}{2}+2-\frac2d$ or $m_2>\frac{m_1-1}{2}+2-\frac2d$, and

$$
(a_{11}^2+a_{12}^2)N_1<16m_1,\qquad
\frac{(a_{11}^2+a_{12}^2)N_1}{m_1}+\frac{(a_{21}^2+a_{22}^2)N_2}{m_2}<16+\frac{(a_{11}a_{22}-a_{12}a_{21})^2N_1N_2}{16m_1m_2}.
$$

   Then there are $C,\lambda>0$ with

$$
\|u(\cdot,t)-N_1\|_{L^2(\mathbb R^d)}+\|v(\cdot,t)-N_2\|_{L^2(\mathbb R^d)}\le Ce^{-\lambda t}\qquad(t>0).
$$

## Expansion

Local existence comes with the blow-up criterion that $\|u\|_\infty+\|v\|_\infty$ must diverge at a finite maximal time. Testing the $u$-equation with powers $u^{p-1}$ produces a dissipation term $\int|\nabla u^{(m_1+p-1)/2}|^2$ from degenerate diffusion and an aggregation term $\int u^{\sigma_1+p-1}(a_{11}u+a_{12}v)$ after using the elliptic equation; a Gagliardo–Nirenberg–Sobolev inequality on $\mathbb R^d$ absorbs the aggregation exactly when diffusion beats aggregation by more than the critical gap $2/d$, which gives uniform $L^p$ and then $L^\infty$ bounds. For stabilization, the choice $\sigma_i=(m_i+1)/2$ makes an entropy-type functional $A(t)+B(t)$ satisfy $\frac{d}{dt}(A+B)\le-\delta F$, where $F$ contains $\int(\nabla u^{(m_1-1)/2}-\frac{m_1-1}{4m_1}\nabla c)^2$, the analogous $v,z$ term, and the squared deviations of $u,v,c,z$ from the constant state. The coefficient conditions are what make the quadratic form in $(\nabla c,\nabla z)$ coercive; combined with boundedness this yields exponential decay in $L^2$.

## Sources

- Shen Bian, "On a two-species Keller-Segel model with degenerate diffusion and two stimuli", arXiv:2607.12472 (2026), Definition 1.1, Theorems 1.2–1.3, Lemmas 2.1–2.2, Proposition 3.1, Lemmas 4.1–4.2, <https://doi.org/10.48550/arXiv.2607.12472>.
