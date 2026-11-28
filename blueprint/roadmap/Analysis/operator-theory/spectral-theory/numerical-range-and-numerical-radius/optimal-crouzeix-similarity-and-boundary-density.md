# Optimal Crouzeix similarity and a common positive boundary density

Let $U\subset\mathbb C$ be nonempty, open, bounded and convex, with Jordan boundary that locally is a holomorphic chart image of the real line and has nonzero chart derivative. The unit disk satisfies these assumptions. For every $a\in U$ there is a holomorphic disk coordinate $f$ on an open neighborhood of $\overline U$, injective with nonzero derivative and a holomorphic inverse on its open image, with $f(a)=0$, $f(U)=\mathbb D$ and image containing the closed disk. There is also an exterior coordinate $G(t)=\alpha t+\beta+h(1/t)$ with $\alpha\ne0$, $h$ holomorphic on a disk of radius $r>1$, and $G$ injective with nonzero derivative on $|t|>1/r$. It maps the unit circle onto $\partial U$, for every $|t|>1/r$, satisfies $G(t)\in U$ if and only if $|t|<1$, and sends $|t|>1$ outside $\overline U$.

For any such coordinates $f,G$ and complex $n$-by-$n$ matrix $A$, $n>0$, with $W(A)=\{\langle x,Ax\rangle:\|x\|=1\}\subset U$ (the inner product is linear in its second argument), put $T=f(A)$, using the analytic matrix calculus (Taylor jets on Jordan blocks). The constraints $I\le H\le\tau I$ and $T^*HT\le H$ in Hermitian order admit a strictly feasible pair (all three slack matrices positive definite). There is $1\le\kappa\le2$ such that the minimum feasible $\tau$ is $\kappa^2$ and is attained. For every minimizing $H$, $S=\sqrt H$ is invertible, $H$ is positive definite, and with $A'=SAS^{-1}$ and $D=STS^{-1}$ one has $D=f(A')$, $D^*D\le I$, $\rho(D)<1$ and $\|S\|\|S^{-1}\|=\kappa$. Every invertible $R$ with $RTR^{-1}$ contractive has condition number at least $\kappa$.

For every such minimizer there is one continuous positive semidefinite $n$-by-$n$ matrix density $\Lambda$ on the unit circle with normalized Haar integral $I$. For every $m>0$ and every $m$-by-$m$ matrix-valued map $V$ analytic on a neighborhood of $\overline U$, complete analytic evaluation entrywise satisfies

$$V[A']=\int_{\mathbb T}\Lambda(t)\otimes V(G(t))\,dt,\qquad \|V[A]\|\le\kappa\sup_{z\in\overline U}\|V(z)\|.$$

The density is selected before the quantifiers over $m,V$.

## Depends on

- Numerical range in the second-argument convention, Hermitian matrix order and analytic evaluation by Jordan jets.
- Holomorphic interior and exterior coordinates extending through the regular Jordan boundary.

## Proof depends on

- Extended conformal mapping, strict feasibility and attainment of the optimal matricial metric, and the positive representing density for the conjugated matrix.

## Expansion

Separate existence of the two coordinates and admissibility of the unit disk from the optimization theorem. Verify similarity invariance and spectral radius control for the analytic calculus, then construct the common density and derive the complete norm bound. Compactness alone of feasible metrics does not prove the condition-number bound or the boundary representation.

## Sources

- OpenAI, [StructuralCrouzeix comparator, challenge](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StructuralCrouzeix.lean#L209-L213).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/325.md).
