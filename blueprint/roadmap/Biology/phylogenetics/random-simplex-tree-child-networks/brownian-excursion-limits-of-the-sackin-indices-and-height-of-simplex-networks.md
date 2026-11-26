# Brownian-excursion limits of the Sackin indices and height of simplex networks

**Setting.** A *simplex tree-child network* on $n$ taxa is a planted binary phylogenetic network (root of in/out-degree $(0,1)$, leaves of degree $(1,0)$ labelled bijectively by the taxa, other vertices tree vertices of degree $(1,2)$ or reticulations of degree $(2,1)$) that is

- *tree-child*: every non-leaf vertex has a child that is a tree vertex or a leaf, and
- *one-component*: every reticulation has a leaf as its unique child.

For a leaf $v$, the shorter height $h^-(v)$ and longer height $h^+(v)$ are the minimal and maximal lengths of a directed root-to-$v$ path. The *shorter and longer Sackin indices* are $S^\pm(N)=\sum_{v\in L(N)}h^\pm(v)$, and the heights are $H^\pm(N)=\max_{v\in L(N)}h^\pm(v)$. Let $\mathcal N_n$ be uniform among simplex networks on $n$ taxa, let $(e(t))_{0\le t\le1}$ be a standard Brownian excursion, and set $\phi_+=\max$, $\phi_-=\min$.

**Theorem (Sackin indices).** Jointly for both signs, as $n\to\infty$,

$$2^{-3/2}n^{-7/4}\,S^\pm(\mathcal N_n)\ \xrightarrow{d}\ L^\pm:=\int_0^1\!\!\int_0^1\phi_\pm\big(e(x),e(y)\big)\,dx\,dy .$$

**Theorem (height).** Jointly, $2^{-3/2}n^{-3/4}\big(H^+(\mathcal N_n),H^-(\mathcal N_n)\big)\xrightarrow{d}\big(\sup_t e(t),\sup_t e(t)\big)$.

**Theorem (tail bound).** There are $C,c>0$ such that for all $n\ge1$, $x\ge0$,

$$\Pr\big(H^-(\mathcal N_n)\ge xn^{3/4}\big)\le\Pr\big(H^+(\mathcal N_n)\ge xn^{3/4}\big)\le Ce^{-cx^2},$$

so all moments converge in the two limits above. The first moments of the limits are

$$\mathbb E L^\pm=\frac{(4\pm1)\sqrt{2\pi}}{16},\qquad \mathbb E (L^\pm)^2=\frac{149\pm70}{336}.$$

**Theorem (height profile).** The leaf-height profiles $\Pi_n^\pm=\frac1n\sum_{v}\delta_{2^{-3/2}n^{-3/4}h^\pm(v)}$ converge jointly in distribution to the image of $\mu_e\otimes\mu_e$ under $\phi_\pm$, where $\mu_e$ is the occupation measure of $e$.

## Expansion

The Cardona–Zhang decomposition writes a simplex network with $k$ tree-parented and $j$ reticulation-parented leaves as a triple: a binary *reduced tree* on $k$ leaves, a composition placing $2j$ reticulation parents along its $2k-1$ edges, and a pairing of those $2j$ attachment points. The number $K_n$ of tree-parented leaves concentrates at order $\sqrt n$ with Gaussian fluctuations of order $n^{1/4}$. Blowing up the reduced tree's edges yields a random plane tree (the top tree component) in the Brownian universality class, whose rescaled contour converges to $e$; every leaf of the network sits at a uniform point of that tree, and a reticulation leaf hangs below two independent uniform points, so its longer and shorter heights are, after rescaling by $2^{-3/2}n^{-3/4}$, the maximum and minimum of $e$ at two independent uniform times. Summing over $n$ leaves gives the $n\cdot n^{3/4}=n^{7/4}$ scale and the double integral of $\phi_\pm$, in contrast with the $n^{3/2}$ scaling and $\int_0^1e$ limit of level-$k$ networks and trees.

## Sources

- Víctor J. Macià, Benedikt Stufler, "Limit laws of random simplex tree-child networks", arXiv:2607.15370: Theorems 1.1 (Sackin indices), 1.2 (height), 1.3 (tail bounds), 1.4 (moments of $L^\pm$), 1.5 (height profile); Proposition 2.1 (decomposition). <https://doi.org/10.48550/arXiv.2607.15370>
