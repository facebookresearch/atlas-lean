# Well-posedness of the 2D stochastic parabolic–parabolic Keller–Segel system with logistic source

**Model.** Let $\mathcal{O} \subset \mathbb{R}^2$ be a bounded smooth domain with outward normal $\mathbf{n}$, and let $W_1, W_2$ be independent cylindrical Wiener processes on $L^2(\mathcal{O})$. The cell density $n$ and chemoattractant $c$ satisfy, for $t \in [0,T]$, $x \in \mathcal{O}$,

$$
\begin{aligned}
dn - \Delta n\,dt + \chi\nabla\cdot(n\nabla c)\,dt &= (\alpha n - \mu n^2)\,dt + g_1(n)\,dW_1(t),\\
dc - \Delta c\,dt &= (n - c)\,dt + g_2(c)\,dW_2(t),
\end{aligned}
$$

with $\mathbf{n}\cdot\nabla n = \mathbf{n}\cdot\nabla c = 0$ on $\partial\mathcal{O}$, where $\chi > 0$, $\alpha \in \mathbb{R}$ (net birth rate) and $\mu > 0$ (logistic damping). The noise is multiplicative and in non-divergence form.

**Assumptions.**
- $g_1 : L^2(\mathcal{O}) \to \mathcal{L}_2(L^2, L^2)$ (Hilbert–Schmidt) is bounded and Lipschitz: $\|g_1(u)\| \le L_0$, $\|g_1(u) - g_1(v)\| \le L_1\|u - v\|_{L^2}$.
- $g_2$ is Lipschitz from $L^2$ and from $W^{1,2}$ into the corresponding Hilbert–Schmidt spaces, acts pointwise-dominated, $|(g_2(u)e_k)(x)| \le |z_k|\,|u(x)|$ with $(z_k) \in \ell^2$, and satisfies a compatible Lipschitz bound in the domain of the fractional Neumann Laplacian on $L^4$.
- Initial laws $\vartheta_1$ on $(L^2(\mathcal{O}))_+$ and $\vartheta_2$ on the nonnegative cone of the Neumann Besov space $B^{3/2}_{4,4}(\mathcal{O})$ have finite 32nd moments.

**Theorem.**
1. (Existence.) There is a global martingale solution $\big((\bar\Omega,\bar{\mathcal F},\bar{\mathbb P},\bar{\mathbb F}), (\bar W_1,\bar W_2), \bar n, \bar c\big)$ with the given initial laws, satisfying the equations weakly in space, with $\bar n \in L^4(\bar\Omega; L^2(0,T;L^2))$, $\bar c \in L^4(\bar\Omega; L^2(0,T; W^{2,2}))$, and $\bar n, \bar c \ge 0$ almost everywhere in $[0,T]\times\mathcal{O}$, $\bar{\mathbb P}$-almost surely.
2. (Uniqueness.) Martingale solutions on a common stochastic basis with the same Wiener processes and almost surely equal initial data coincide for all $t \in [0,T]$ almost surely (pathwise uniqueness); martingale solutions with the same initial law have the same law (uniqueness in law).
3. (Strong solutions.) For random initial data $n_0 \in L^{32}(\Omega; (L^2)_+)$, $c_0 \in L^{32}(\Omega; (B^{3/2}_{4,4})_+)$, there is a unique global nonnegative probabilistically strong (weak-in-space) solution, with no smallness condition on the data.

## Expansion

In two dimensions the deterministic fully parabolic Keller–Segel system can blow up for supercritical mass, and the logistic damping $-\mu n^2$ is what prevents aggregation; the result shows that this stabilization survives multiplicative noise. The construction regularizes the chemotactic flux, solves the regularized system by a Banach fixed point with stopping-time localization, and proves nonnegativity by applying the Itô formula to $C^2$ approximations of the negative-part functional, where the pointwise domination of $g_2$ controls the stochastic term. Because the cross-diffusion is too strong for uniform moment bounds on the density in high norms, tightness is obtained from uniform bounds *in probability*, which suffice for the Jakubowski–Skorokhod representation theorem and passage to the limit. Pathwise uniqueness, together with existence of martingale solutions, then yields uniqueness in law and a unique probabilistically strong solution.

## Sources

- Erika Hausenblas, Boris Jidjou Moghomye and Paul Andre Razafimandimby, "Well-posedness of 2D stochastic parabolic-parabolic Keller-Segel system with logistic source", arXiv:2610.22458 (2026), Section 2, Assumption 2.1, Definitions 2.3–2.4 and Theorems 2.5–2.6, <https://doi.org/10.48550/arXiv.2610.22458>.
