# Matrix Riccati models of social balance

**Social balance.** Let $X(t) \in \mathbb R^{n\times n}$ hold reputations on a complete graph, $X_{ij} > 0$ meaning $i$ regards $j$ as a friend and $X_{ij} < 0$ as a foe. The network is **balanced** if, after relabelling, the sign pattern of $X$ is $\begin{pmatrix} + & - \\ - & + \end{pmatrix}$ in block form (or all positive): equivalently, every triad is balanced and the individuals split into at most two factions. A rank-one matrix $ww^{\mathsf T}$ with $w$ having no zero entries is balanced, with factions given by the signs of $w$.

**Two gossip models.**

$$\text{(A)}\quad \dot X = X^2, \qquad \dot X_{ij} = \sum_k X_{ik}X_{kj}; \qquad\qquad \text{(B)}\quad \dot X = XX^{\mathsf T}, \qquad \dot X_{ij} = \sum_k X_{ik}X_{jk}.$$

In (A) $i$ updates its view of $j$ by asking every $k$ what $k$ thinks of $j$; in (B) $i$ asks $j$ what $j$ thinks of everyone and compares it with its own views.

**Theorem.**
1. (Model A, normal data.) If $X(0)$ is normal ($XX^{\mathsf T} = X^{\mathsf T}X$) with a real, simple, positive eigenvalue $\lambda_1(0)$ exceeding every other real eigenvalue, then $X(t)$ blows up at $t^* = 1/\lambda_1(0)$ and $X(t)/\|X(t)\|_F \to u_1u_1^{\mathsf T}$ as $t \to t^*$, where $u_1$ is the unit eigenvector; so the normalized network becomes balanced when $u_1$ has no zero entries. For symmetric $X(0)$, blow-up happens if and only if $\lambda_1(0) > 0$.
2. (Model A, generic data.) If $X(0)$ is not normal, under the same eigenvalue hypothesis $X(t)/\|X(t)\|_F \to u_1 v_1^{\mathsf T}/\|u_1 v_1^{\mathsf T}\|_F$ with $u_1, v_1$ the right and left eigenvectors, a rank-one limit whose sign pattern is generically not balanced.
3. (Model B.) Writing $X = S + A$ with $S$ symmetric and $A$ skew, $A(t) \equiv A(0)$ is conserved and $S$ obeys a matrix Riccati equation that integrates explicitly. If $A(0) \ne 0$ the solution always blows up in finite time, and for a dense set of initial conditions $X(t)/\|X(t)\|_F \to ww^{\mathsf T}/\|w\|^2$ as $t \to t^*$, so the network generically becomes balanced in finite time.

## Depends on

- [Structural balance of complete signed graphs](../../../../GraphTheory/social-networks/structural-balance-of-complete-signed-graphs.md)

## Proof depends on

- [Spectral theorem for normal matrices](../../../../LinearAlgebra/eigenvalues-and-canonical-forms/spectral-theorem-for-normal-matrices/exists-unitary-diagonal-of-is-star-norma.md)

## Expansion

For symmetric data, model A decouples in an orthonormal eigenbasis into scalar equations $\dot\lambda = \lambda^2$ with solutions $\lambda(t) = \lambda(0)/(1 - \lambda(0) t)$, so the largest positive eigenvalue explodes first and its eigenprojection dominates; for non-normal data the same dominance holds in the Jordan basis but produces $u_1 v_1^{\mathsf T}$, whose two sign vectors need not agree. In model B, $\frac{d}{dt}(X - X^{\mathsf T}) = XX^{\mathsf T} - XX^{\mathsf T} = 0$, which removes the asymmetry from the dynamics and leaves a symmetric Riccati flow whose blow-up direction is a single symmetric rank-one matrix. Read as cooperation ($X_{ij} > 0$ means $i$ cooperates with $j$), model B corresponds to judging others by how they treat third parties, the indirect-reciprocity mechanism; in evolutionary simulations of a donation game with fixation probabilities as the readout, agents updating by model B outcompete those using model A and resist unconditional defectors once the benefit-to-cost ratio exceeds a threshold that grows with group size.

## Sources

- V. A. Traag, P. Van Dooren, P. De Leenheer, "Dynamical models explaining social balance and evolution of cooperation", PLoS ONE 8(4): e60063 (2013), Eqs 1–8 and Supporting Text S1 Theorems 2, 3 and 5, <https://doi.org/10.1371/journal.pone.0060063>, PMCID PMC3636264.
