# Long branch attraction for the distance to stochastic phylogenetic regions

**Setting.** Use the quartet trees $\mathcal T$, stochastic regions $\mathcal V_T^+$ and Euclidean distance of [the closest stochastic point for a non-stochastic interior edge](closest-stochastic-point-for-a-non-stochastic-interior-edge.md), now under the Jukes–Cantor (JC69) model. A JC69 matrix is determined by its eigenvalue different from $1$; write $\varphi_T(x_1,\dots,x_5)$ for the joint distribution (in Fourier coordinates) on $T$ whose pendant edges $1,\dots,4$ and interior edge carry JC69 matrices with these eigenvalues, and recall that a JC69 matrix is stochastic exactly when its eigenvalue lies in $I=[-1/3,1]$. Let

$$
\omega=\tfrac49+\frac{11}{27\,\sqrt[3]{(69+16\sqrt3)/243}}+\sqrt[3]{(69+16\sqrt3)/243}\approx1.734,\qquad \Omega=(1,\omega].
$$

For $(k,m)\in I\times\Omega$, the long-branch-attraction point $P_0=\varphi_{12|34}(k,1,k,1,m)$ has a stochastic matrix with eigenvalue $k$ on the two non-sister pendant edges $1$ and $3$, identity on edges $2$ and $4$, and a non-stochastic interior matrix with eigenvalue $m>1$. Let $\tilde x(k,m)$ be the unique real critical point of $x\mapsto d(P_0,\varphi_T(x,1,x,1,1))^2$ (the same function for all three $T$; explicit formula in the source).

**Theorem (local minimum).** For $k\in[-1/3,1]$ and $m\in\Omega$, the point $(\tilde x(k,m),1,\tilde x(k,m),1,1)$ (with $\tilde x$ replaced by $1$ when $\tilde x(k,m)\ge1$) is a local minimum of the problem of minimizing $d(P_0,\varphi_T(\mathbf x))^2$ over $\mathbf x\in[-1/3,1]^5$, for every $T\in\mathcal T$.

**Theorem (long branch attraction).** Let $T=12|34$, $(k_0,m_0)\in I\times\Omega$, and assume the distance from $P_0=\varphi_T(k_0,1,k_0,1,m_0)$ to $\mathcal V_T^+$ is attained at the unique point $P_0^+=\varphi_T(\tilde x(k_0,m_0),1,\tilde x(k_0,m_0),1,1)$ with $\tilde x(k_0,m_0)\ne0$. Then for every $P$ close enough to $P_0$ and every $T'\ne T$ in $\mathcal T$, the closest point to $P$ in $\mathcal V_T^+$ also lies in $\mathcal V_{T'}^+$; in particular

$$
d(P,\mathcal V_T^+)\ \ge\ d(P,\mathcal V_{T'}^+).
$$

The uniqueness hypothesis is stated in the source as a conjecture (Conjecture 6.4) supported by numerical evidence.

## Expansion

The minimizer replaces the non-stochastic interior eigenvalue $m>1$ by $1$, i.e. it contracts the interior edge to length zero. A star-like distribution with a zero-length interior edge belongs to the stochastic region of every quartet topology, so the true tree gains no advantage, and nearby perturbations can make a wrong tree strictly closer. This is a long-branch-attraction phenomenon: in contrast to the short-external-branch case, choosing the topology by distance to the stochastic regions is not consistent near these points. The local-minimum statement is proved from the Karush–Kuhn–Tucker conditions for the box constraints $-1/3\le x_i\le1$; simulations in the source compare distance-based reconstruction with maximum likelihood on such data.

## Depends on

- [Closest stochastic point to a quartet distribution with a non-stochastic interior edge](closest-stochastic-point-for-a-non-stochastic-interior-edge.md)

## Sources

- Marta Casanellas, Jesús Fernández-Sánchez, Marina Garrote-López. *Distance to the stochastic part of phylogenetic varieties* (2019), Sections 2–4 and 6: Definition 3.1, Lemmas 3.2 and 3.4, Proposition 4.1, Theorem 4.3, Theorem 6.3, Conjecture 6.4 and Theorem 6.6. <https://doi.org/10.48550/arXiv.1912.02138>
