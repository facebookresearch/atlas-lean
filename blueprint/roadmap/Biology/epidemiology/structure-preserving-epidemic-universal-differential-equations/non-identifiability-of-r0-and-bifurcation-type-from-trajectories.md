# Non-identifiability of R0 and bifurcation type from epidemic trajectories

**Setting.** Consider a structure-preserving epidemic model whose transmission is a learned closure $\beta(x)$ (bounded by $\bar G$) inside a factorized force of infection, with rank-one next-generation matrix so that
$$\mathcal R_0(\beta)=z^*_{s_*}\,\beta(E_0)^{\mathsf T}\,V^{-1}w$$
depends only on the value of the closure at the disease-free equilibrium $E_0$. Two closures are **indistinguishable on a set** $\Gamma$ of states if their vector fields agree on $\Gamma$; a functional is **identifiable from data on $\Gamma$** if it agrees for indistinguishable closures.

**Theorem (non-identifiability).** Let $\Gamma\subset\Omega$ be compact with $d=\operatorname{dist}(E_0,\Gamma)>0$, for example the closure of an observed epidemic trajectory whose $\omega$-limit set avoids $E_0$. For any admissible closure $\beta^{(1)}$ and any constant vector $\beta^\circ\in[0,\bar G]^m$ there is an admissible $\beta^{(2)}$ of the same regularity with $\beta^{(2)}=\beta^{(1)}$ outside the ball $B_{d/2}(E_0)$, so the two models produce the same solutions on $\Gamma$, but $\beta^{(2)}(E_0)=\beta^\circ$. Hence $\mathcal R_0(\beta^{(2)})$ takes every value in $[0,\bar G z^*_{s_*}\mathbf 1^{\mathsf T}V^{-1}w]$: $\mathcal R_0$ is not identifiable from data away from the disease-free state. Both closures can be approximated arbitrarily well in $C^1$ by neural network closures.

**Theorem (quantitative identifiability).** If two $L_\beta$-Lipschitz closures differ by at most $\varepsilon$ on $\Gamma$, then
$$|\mathcal R_0(\beta^{(1)})-\mathcal R_0(\beta^{(2)})|\le z^*_{s_*}\,\mathbf 1^{\mathsf T}V^{-1}w\,(\varepsilon+2L_\beta d).$$
So uncertainty in $\mathcal R_0$ is controlled by closure regularity times the distance from the observations to $E_0$; if $E_0$ is among the observed states the spread is at most $2\varepsilon z^*_{s_*}\mathbf 1^{\mathsf T}V^{-1}w$. Monotonicity of the closure gives one-sided bounds from data at a single state.

**Corollary (bifurcation type).** For the neural SEIR model with prevalence-dependent $\beta(I)$ and data on a set where $I\ge d_I>0$, the value $\beta(0)$ and slope $\beta'(0)$ can be prescribed independently while keeping $\beta$ unchanged for $I\ge d_I/2$. Since $\mathcal R_0$ depends on $\beta(0)$ and the bifurcation is backward iff $\beta'(0)/\beta(0)>(\mu+\sigma)(\mu+\gamma+\delta)/(\sigma\Lambda)$, two closures indistinguishable on the data can share the same $\mathcal R_0$ yet undergo forward and backward bifurcations respectively.

## Depends on

- [Threshold dynamics of flux-closure epidemic models](threshold-dynamics-of-flux-closure-epidemic-models.md)

## Expansion

The construction is a smooth cutoff: with $\chi$ a bump equal to $1$ near $E_0$ and $0$ outside $B_{d/2}(E_0)$, set $\beta^{(2)}=(1-\chi)\beta^{(1)}+\chi\beta^\circ$, a convex combination that remains admissible. Because the observed states never come near $E_0$, the data constrain the closure only where it does not determine $\mathcal R_0$, which is a local quantity at the disease-free state. The Lipschitz bound follows from $|\beta^{(1)}(E_0)-\beta^{(2)}(E_0)|\le\varepsilon+2L_\beta d$ by passing through the nearest observed state, then using linearity of $\mathcal R_0$ in $\beta(E_0)$. The practical message for scientific machine learning in epidemiology is that properties at the invasion threshold require data near the disease-free state, or monotonicity priors on the learned transmission.

## Sources

- A. Alsammani, M. Martcheva, "Structure-preserving universal differential equations for epidemic dynamics", arXiv:2611.23291 (2026), Section 11 (Theorem 11.1, Definition 11.2, Theorems 11.3-11.4, Corollaries 11.6-11.7, Proposition 11.8) and Section 9 (Corollary 9.2), <https://doi.org/10.48550/arXiv.2611.23291>.
