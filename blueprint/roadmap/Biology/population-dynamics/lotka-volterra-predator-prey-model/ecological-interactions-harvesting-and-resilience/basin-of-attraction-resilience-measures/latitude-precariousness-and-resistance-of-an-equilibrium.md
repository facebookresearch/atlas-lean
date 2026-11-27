# Latitude, precariousness and resistance of an equilibrium

Let $X'=F(X)$, $X\in\mathbb R^2$, with $F\in C^1$, have an asymptotically stable equilibrium $P$ with basin of attraction $\mathcal A(P)$, and fix a bounded region of interest $C$ of positive area containing the relevant attractors. Three measures quantify the resilience of $P$:

- **Latitude** (size of the basin):

$$L(P)=\frac{\operatorname{Area}\bigl(\mathcal A(P)\cap C\bigr)}{\operatorname{Area}(C)}\in[0,1].$$

If the only attractors in $C$ are $P$ and $Q$ and the separatrix has zero area, then $L(P)+L(Q)=1$; a globally stable equilibrium has latitude $1$.

- **Precariousness** (smallest perturbation that leaves the basin): for a set $Z(P)$ of biologically relevant perturbation directions,

$$Pr(P)=\inf\bigl\{\operatorname{dist}(P,X):X\in\partial\mathcal A(P)\cap Z(P)\bigr\},$$

which reduces to the Euclidean distance from $P$ to the basin boundary when $Z(P)$ is the whole plane.

- **Resistance** (depth of the basin): with the instantaneous Jacobian $\mathcal J_{dt}(X)=I+J(X)\,dt$, local Lyapunov exponents $\lambda_i(X)=\frac{1}{dt}\ln\sigma_i(X)$ from the singular values $\sigma_i(X)$ of $\mathcal J_{dt}(X)$, and local resistance $R(X)=-\max_i\lambda_i(X)$,

$$Res(P)=\frac{\iint_{\mathcal A(P)\cap C}R(X)\,dX}{\iint_CR(X)\,dX}.$$

**Computing the latitude.** When $\partial\mathcal A(P)\cap C$ is made of the stable separatrix (stable invariant curve) $S$ of a saddle $X^*$ and segments $L_i$ of $\partial C$, Green's theorem gives

$$\operatorname{Area}\bigl(\mathcal A(P)\cap C\bigr)=\oint_{\partial(\mathcal A(P)\cap C)}x_1\,dx_2=\int_Sx_1\,dx_2+\sum_i\int_{L_i}x_1\,dx_2,$$

where $S$ is approximated by a power series: diagonalize $J=F'(X^*)=M\operatorname{diag}(k_{11},k_{22})M^{-1}$ with $k_{11}<0<k_{22}$, set $U=M^{-1}(X-X^*)=(u,v)$, write the stable invariant curve as $v=p(u)=c_2u^2+c_3u^3+\cdots$, and determine the $c_j$ recursively from the invariance equation $p'(u)f(u,p(u))=g(u,p(u))$, where $(f,g)$ is the vector field in $U$ coordinates.

## Expansion

Latitude measures robustness to random state perturbations (a large basin is hard to leave by chance), precariousness measures how close the state already is to a tipping boundary in the directions perturbations actually take, and resistance measures how strongly the flow pulls perturbed states back, i.e. how many small perturbations are absorbed before a transition. In a bistable tumour–normal tissue model the latter matters for therapy: a more resistant cancer equilibrium needs more or larger treatment doses to be pushed into the basin of the cure equilibrium. For $\sigma_i$: as $dt\to0$, $\lambda_i(X)$ tends to the eigenvalues of the symmetric part $\frac12(J+J^\top)$, so $R(X)$ is minus the largest instantaneous stretching rate.

## Proof depends on

- [Green's theorem](../../../../../Analysis/real-functions/multivariable-calculus/greens-theorem.md)

## Sources

- A. C. Fassoni and H. M. Yang, *An ecological resilience perspective on cancer: insights from a toy model*, arXiv:1604.08921 (2016), Section 5 (Sections 5.1–5.3). <https://doi.org/10.48550/arXiv.1604.08921>
