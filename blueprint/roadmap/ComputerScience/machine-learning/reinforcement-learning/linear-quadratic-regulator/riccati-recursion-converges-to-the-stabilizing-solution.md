# The Riccati recursion converges to the stabilizing solution

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{q \times n}$, put $Q = C^\top C$, and let $R \in \mathbb{R}^{m \times m}$ be positive definite. Let

$$\mathcal{R}(M) = Q + A^\top M A - A^\top M B (R + B^\top M B)^{-1} B^\top M A.$$

The inverse exists for positive semidefinite $M$. Say that $(A,B)$ is **stabilizable** if some $F$ makes $A+BF$ convergent (all eigenvalues have modulus less than $1$), and that $(C,A)$ is **detectable** if some $L$ makes $A+LC$ convergent.

1. **Zero terminal cost, without detectability.** If $(A,B)$ is stabilizable, the sequence $M_0=0$, $M_{j+1}=\mathcal{R}(M_j)$ is nondecreasing and bounded above in the positive semidefinite order. It converges to a positive semidefinite matrix $P$ satisfying $P=\mathcal{R}(P)$.
2. **Arbitrary terminal cost and stability.** If, in addition, $(C,A)$ is detectable, then for every positive semidefinite initial matrix $M_0$ the same recursion converges to the $P$ in part 1. With

    $$K=(R+B^\top P B)^{-1}B^\top P A,$$

    the closed-loop matrix $A-BK$ is convergent. Under these two hypotheses, $P$ is the only positive semidefinite solution of the algebraic Riccati equation. For each $M_0$ there are constants $a\ge0$ and $0<\theta<1$ such that $\|M_j-P\|\le a\theta^j$ for all $j\ge0$, in the Euclidean operator norm; no optimal rate is asserted.

3. **Uniqueness among stabilizing solutions, without detectability.** Independently of the detectability hypothesis, if $P_1,P_2$ are positive semidefinite fixed points and both $A-BK_i$ are convergent, where $K_i=(R+B^\top P_iB)^{-1}B^\top P_iA$, then $P_1=P_2$. This does not assert uniqueness among nonstabilizing or indefinite solutions.

For parts 1 and 2, use the source's filtering equation with $F=A^\top$, $H=B$, process-noise matrix $G=C^\top$ and process-noise covariance $I_q$, keeping the same $R$. The variance equation becomes $M_{j+1}=\mathcal{R}(M_j)$. Detectability of the filter's observation pair $(H^\top,F)$ becomes stabilizability of $(A,B)$; stabilizability of its process pair $(F,G)$ becomes detectability of $(C,A)$. The steady prediction gain is $K_{\mathrm f}=A^\top P B(R+B^\top P B)^{-1}=K^\top$, and

$$F-K_{\mathrm f}H^\top=(A-BK)^\top.$$

The transpose is important: the two closed-loop matrices have the same spectrum, not the same orientation.

The bound by a stabilizing suboptimal gain and monotonicity from zero use only stabilizability of $(A,B)$. They give part 1, and continuity of the update on positive semidefinite matrices gives the fixed-point property. Detectability of $(C,A)$ is used for stability in part 2. The source then proves convergence from $M_0=\rho I$ using its covariance-difference identity and a bounded time-varying transition matrix, and sandwiches a general $0\preceq M_0\preceq\rho I$ between the zero and $\rho I$ starts. A different positive semidefinite fixed point would give a constant sequence, contradicting this common limit. For the stated geometric bound, the derivative at $P$ is $E\mapsto(A-BK)^\top E(A-BK)$, whose spectral radius is $\rho(A-BK)^2<1$. A local contraction in an equivalent norm, after the already-proved convergence, gives the bound in the Euclidean operator norm. This argument does not assume diagonalizability or an exact bound with base $\rho(A-BK)$.

Part 3 is the following calculation, not an attribution to the source's stronger-hypothesis uniqueness argument. For any positive semidefinite $M_1,M_2$, put $K_i=(R+B^\top M_iB)^{-1}B^\top M_iA$. Expanding and using $(R+B^\top M_iB)K_i=B^\top M_iA$ gives

$$\mathcal{R}(M_1)-\mathcal{R}(M_2)=(A-BK_1)^\top(M_1-M_2)(A-BK_2).$$

For fixed points, $X=P_1-P_2$ therefore satisfies

$$X=((A-BK_1)^\top)^j X(A-BK_2)^j \qquad(j\ge0).$$

Both matrix powers tend to zero, so $X=0$.

## Depends on

- [Riccati update](riccati-map.md): the map whose iterates and fixed points are studied.
- [Riccati recursion](riccati-cost-to-go.md): the iterates with terminal cost $M_0$.
- [Riccati gain](riccati-gain.md): the closed-loop gain $K$.

## Proof depends on

- [The Riccati update preserves positive semidefiniteness](riccati-map-pos-semidef.md): the iterates stay in the domain where the inverses exist.
- [Hautus test for stabilizability and detectability, discrete time](../../../../Analysis/control-theory/pole-placement/hautus-test-for-stabilizability-and-detectability-discrete-time.md): duality of the control and observation hypotheses and the stable-mode argument.

- [Exponential stability of linear difference equations](../../../../Analysis/ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-difference-equations.md): powers of the two stabilizing closed-loop matrices tend to zero; the same spectral criterion applies to the derivative operator.

## Sources

- B. D. O. Anderson and J. B. Moore, *Optimal Filtering*, Prentice-Hall, 1979, <https://users.cecs.anu.edu.au/~john/papers/BOOK/B02.PDF>, Section 4.4, pp. 76–83: equations (4.1)–(4.6); the suboptimal-filter bound and monotonicity from zero (pp. 78–80, using complete detectability of the filter's observation pair); the steady-state stability argument using complete stabilizability of its process pair; convergence from nonzero initial covariances (pp. 81–82); and uniqueness of the nonnegative definite solution under both hypotheses (p. 82). The footnote on p. 77 excludes singular innovation covariance; positive definite $R$ ensures nonsingularity here. Part 3 and the explicit derivative justification of the geometric bound are proved above.
