# Spheres of real trees as coalescent point processes

**Setting.** Let $\mathbf t$ be a compact (or locally compact) rooted real tree, and for $T>0$ let $\mathbf t^{\{T\}}$ be its **sphere of radius $T$**: the points at distance exactly $T$ from the root, i.e. the population alive at time $T$ in a genealogy started at time $0$. With the tree metric, $d(x,y)=2(T-\text{height of the most recent common ancestor of }x,y)$ for $x,y\in\mathbf t^{\{T\}}$, so the sphere is a compact ultrametric space. Let $h$ be the jumping contour process of the tree truncated at height $T$ and $p_h$ the canonical projection from contour time to the tree.

**Theorem (comb of a sphere).** Assume $\mathbf t^{\{T\}}$ is nonempty and has no isolated point. Then $\{h=T\}$ is a perfect set with empty interior, so $h$ has a continuous local time $L$ at level $T$; let $I=[0,L_{\sigma_h}]$, $J$ the right-continuous inverse of $L$, and for each jump time $s$ of $J$ let $(g_s,d_s)=(J_{s-},J_s)$ be the corresponding excursion interval of $h$ below $T$. Define the comb

$$
f(s)=\begin{cases}2\big(T-\inf_{[g_s,d_s]}h\big), & \Delta J_s\ne 0,\\ 0, & \text{otherwise.}\end{cases}
$$

Then the comb metric space $(\bar I,d_f)$ is globally isometric to $(\mathbf t^{\{T\}},d)$, by an order-preserving isometry that maps Lebesgue measure on $I$ to the push-forward of $dL$ by $p_h$. In words: the genealogy of the population at time $T$ is the list of depths of the excursions of the contour process away from $T$.

**Coalescent point process.** Let $\nu$ be a $\sigma$-finite measure on $(0,\infty)$ with $\nu([\varepsilon,\infty))<\infty$ for all $\varepsilon>0$, let $(S_i,H_i)$ be the atoms of a Poisson point process on $(0,\infty)^2$ with intensity $\mathrm{Leb}\otimes\nu$, and let $(D,H)$ be the first atom (in the first coordinate) with $H>T$. The random comb metric space of $\sum_{i:S_i<D}2H_i\mathbf 1_{\{S_i\}}$ is the **coalescent point process** with height $T$ and intensity $\nu$. When $h$ is a strong Markov process for which $T$ is regular, the excursions of $h$ away from $T$ form a Poisson point process, so the sphere of radius $T$ is a coalescent point process with $\nu$ the image of the excursion measure under the depth map $e\mapsto T-\inf e$ (the comb $f$ above is $2H$ at each atom, so $H$ is the depth, not twice it).

**Theorem (Brownian tree; Popovic, Aldous–Popovic).** For the Brownian continuum random tree (coded by a Brownian excursion conditioned to reach height $T$), the sphere $\mathbf t^{\{T\}}$ is a coalescent point process with height $T$ and intensity

$$
\nu(dh)=\frac{dh}{2h^2}.
$$

## Depends on

- [Comb representation of compact ultrametric spaces](comb-metric-spaces-represent-compact-ultrametric-spaces.md)

## Expansion

For a finite sphere $x_1\le\dots\le x_N$ in contour order, $d(x_i,x_j)=h(s_i)+h(s_j)-2\inf_{[s_i,s_j]}h=2\max(h_i,\dots,h_{j-1})$ with $h_i=T-\inf_{[s_i,s_{i+1}]}h$, which is already a comb metric. In general, absence of isolated points rules out isolated zeros of $h-T$ and intervals where $h\equiv T$ (the latter would give the mass measure an atom), so a local time at $T$ exists. Between two times $s<t$ of $\dot I$, $d(p_h(J_s),p_h(J_t))=2\sup_{[J_s,J_t]}(T-h)$, and this supremum is attained inside one excursion below $T$, giving $\sup_{[s,t]}f=d_f(s,t)$; the two faces of a jump time correspond to the two endpoints $J_{s-},J_s$ of the excursion. The Brownian case follows because the excursion measure of reflected Brownian motion assigns mass proportional to $1/h$ to excursions of depth at least $h$, so $\nu([h,\infty))=1/(2h)$ and $\nu(dh)=dh/(2h^2)$. Splitting trees and, more generally, trees whose truncated contours are spectrally positive Lévy processes give coalescent point processes in the same way.

## Sources

- Amaury Lambert and Gerónimo Uribe Bravo, *The comb representation of compact ultrametric spaces*, p-Adic Numbers Ultrametric Anal. Appl. 9(1) (2017), 22–38. <https://doi.org/10.1134/S2070046617010034> Section 4 (Lemma 4.1, Theorem 4.2, Definition 4.4 of the coalescent point process, Theorem 4.5 citing Popovic and Aldous–Popovic for the Brownian tree). Locators use the numbering of the preprint arXiv:1602.08246.
