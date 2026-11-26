# Bessel-zero secondary critical mass of radial Keller–Segel in a ball

**Setting.** Let $n\ge2$, $R>0$ and consider the parabolic–elliptic Keller–Segel system in the ball $B_R\subset\mathbb{R}^n$,

$$
u_t=\Delta u-\nabla\cdot(u\nabla v),\qquad 0=\Delta v-\mu+u,\quad \mu=\frac{1}{|B_R|}\int_{B_R}u_0,
$$

with homogeneous Neumann conditions and radially symmetric initial data $u_0\in C^0(\bar B_R)$, $u_0\ge0$, of mass $m=\int_{B_R}u_0$. Let $\omega_n=n|B_1|$ and let $\xi_*(n)$ be the first positive zero of the Bessel function $J_{n/2}$. Define

$$
m_*(n,R)=\frac{\omega_nR^{n-2}}{n}\,\xi_*^2(n).
$$

**Theorem.**
1. If $m<m_*(n,R)$, there are $\varepsilon,\alpha>0$ such that every radial $u_0$ of mass $m$ with $\|u_0-m/|B_R|\|_{L^\infty}\le\varepsilon$ yields a unique global classical solution with $\|u(\cdot,t)-m/|B_R|\|_{L^\infty}\le Ce^{-\alpha t}$ for all $t>0$.
2. If $m>m_*(n,R)$, every radial $u_0$ of mass $m$ that is more concentrated than the constant state, i.e. $\frac{1}{|B_r|}\int_{B_r}u_0\ge\frac{m}{|B_R|}$ for all $r\in(0,R)$ with $u_0\not\equiv m/|B_R|$, produces a solution that blows up in finite time.

**Corollary (sharp secondary critical mass).** Among radial data more concentrated than the constant state, let $\overline m_c$ be the infimum of masses at which all such data blow up in finite time, and $\underline m_c$ the supremum of masses at which some such datum has a global bounded solution. Then $\overline m_c(n,R)=\underline m_c(n,R)=m_*(n,R)$ for all $n\ge2$, $R>0$.

## Expansion

In the radial mass-accumulation variable $w(s,t)=\int_{B_{s^{1/n}}}u\,dx/\omega_n$ the system becomes a scalar degenerate parabolic equation, and the constant steady state is $w=\mu s/n$. Linearizing around it leads to the eigenvalue problem $s\Theta''+2\Theta'=-\frac{\xi^2}{n^2R^2}s^{2/n-1}\Theta$, solved by $\Theta(s)=s^{-1/2}J_{n/2}(\xi s^{1/n}/R)$; the first positive Bessel zero gives the smallest mass at which the constant state loses linear stability. Below $m_*$, multiples of $s\Theta(s)$ give decaying sub- and supersolutions that trap $w$ near $\mu s/n$; above $m_*$, concentration ordering is preserved by comparison and drives $w$ to a singular profile. For $n=2$, $m_*$ is independent of $R$, while the classical critical mass $8\pi$ governs blow-up for general data; $m_*$ is a second threshold specific to perturbations of the homogeneous state.

## Sources

- Yulan Wang, Michael Winkler, "Identifying secondary critical mass levels in two- and higher-dimensional Keller-Segel systems", arXiv:2610.13559: Section 1 (Introduction): Theorem 1.1 and Corollary 1.2; Lemmas on the Bessel comparison function, exponential stabilization below and blow-up above the threshold. <https://doi.org/10.48550/arXiv.2610.13559>
