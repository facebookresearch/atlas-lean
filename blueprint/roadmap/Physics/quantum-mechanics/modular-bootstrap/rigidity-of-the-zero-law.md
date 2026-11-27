# Rigidity of the limiting zero law for slope-attaining functionals

Let $c_j\ge40$ tend to $+\infty$, $c'_j=c_j-1$, and let each $g_j\in\overline{\mathcal A}\setminus\{0\}$ at charge $c_j$ be weakly feasible. Assume its scaled last sign threshold $x_1(g_j)=\sqrt{3t_1(g_j)/c'_j}$ tends to $x_*$. Under the paper's contact result it suffices to require $\limsup_j x_1(g_j)\le x_*$. Attaining sequences exist by the explicit attainment theorem.

On the [fixed strip $S$](strip-potential-and-zero-law.md), write $G_j(b)=g_j(c'_j b^2/3)$ for the even holomorphic continuation from the radial kernel. Its profile and zero-counting measure are

$$
u_j(b)=\frac{1}{c'_j}\log\frac{|G_j(b)|}{M[g_j]},\qquad
\mathfrak n_j=\frac{1}{c'_j}\sum_{\zeta\in S:G_j(\zeta)=0}m_\zeta\,\delta_\zeta,
$$

where $m_\zeta$ is multiplicity; at a zero the profile is $-\infty$ and is interpreted as locally integrable. Along the **whole sequence** $u_j\to U$ in $L^1_{\mathrm{loc}}(S)$, and $\mathfrak n_j$ converges vaguely on $S$ to $\rho_U(x)\,dx\otimes\delta_0(dy)$ supported on the slits $|x|\ge x_*$. In particular compact sets disjoint from the slits contain $o(c'_j)$ zeros. For every fixed $x_*<x_a<x_b$ and $0<y_0<1/2$, the number in $[x_a,x_b]\times[-y_0,y_0]$ is

$$
c'_j\int_{x_a}^{x_b}\rho_U(x)\,dx+o(c'_j).
$$

The number of zeros of the continued $g_j$ in the image of that rectangle under $b\mapsto c'_j b^2/3$, with multiplicity, is

$$
c'_j\int_{\xi_a}^{\xi_b}2\rho_V(\xi)\,d\xi+o(c'_j),\qquad
\xi=\frac{x^2}{3},\quad \xi_a=\frac{x_a^2}{3},\quad \xi_b=\frac{x_b^2}{3},\quad
\rho_V(\xi)=\frac{3\rho_U(x)}{4x}\quad(x> x_*).
$$

The image lies in $|\operatorname{Im} t|\le (2/3)c'_j x_b y_0$. Neither this theorem nor its density formulas force individual zeros to be real or paired, bound rates, or describe the strip edges, zeros outside the strip, or fine structure at the tip. The paper proves the rigidity implication by hand.

## Depends on

- [Weakly feasible functional class, mass and last sign threshold](functional-class.md)
- [Slit-strip potential and limiting density](strip-potential-and-zero-law.md)

## Proof depends on

- [Cardy-mass concentration](cardy-mass-concentration.md)

## Expansion

Establish the holomorphic extension and the normalized Riesz identity $(2\pi)^{-1}\Delta u_j=\mathfrak n_j$. Use subharmonic compactness, the universal majorant, and weak feasibility to obtain a contact point at the tip for every subsequential limit; rule out escape to $-\infty$. The slit-tip harmonic-measure lower bound and the $3/2$-order deficit then force every limit to equal $U$. Pass to continuous compactly supported tests for vague convergence; the rectangle's boundary carries no limit charge. The square map is injective and locally invertible on the positive-real-part rectangle, so it preserves multiplicity and $2\rho_V(\xi)d\xi=\rho_U(x)dx$.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [§10.1, (10.1), contact and compactness, p. 64](https://hexagonmath.org/pdf/2611.00174v1#page=64).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Theorem 7 and (10.2)–(10.3), p. 65](https://hexagonmath.org/pdf/2611.00174v1#page=65).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Appendix I.4, proof of Theorem 7, pp. 125–127](https://hexagonmath.org/pdf/2611.00174v1#page=125).
