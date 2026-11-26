# Sum-check polynomial for folding an LCCCS and a CCCS instance

Let $(C_1,u,x_1,r_x,v_1,\dots,v_t)$ be an LCCCS instance with witness $z_1$ and $(C_2,x_2)$ a CCCS instance with witness $z_2$. For verifier challenges $\gamma\in\mathbb{F}$ and $\beta\in\mathbb{F}^{s}$ define

$$
g(X)=\sum_{j=1}^{t}\gamma^{j}L_j(X)+\gamma^{t+1}Q(X),
$$

with $L_j(X)=\widetilde{\mathrm{eq}}(r_x,X)\sum_{y}\widetilde{M}_j(X,y)\widetilde{z}_1(y)$ and $Q(X)=\widetilde{\mathrm{eq}}(\beta,X)\sum_{i=1}^{q}c_i\prod_{j\in S_i}\bigl(\sum_{y}\widetilde{M}_j(X,y)\widetilde{z}_2(y)\bigr)$. If both inputs are satisfying, then $\sum_{X\in\{0,1\}^{s}}g(X)=\sum_{j}\gamma^{j}v_j$. Conversely, if the CCCS input is not satisfying, then over random $\beta$ and $\gamma$ the identity holds with probability at most $(s+t+1)/|\mathbb{F}|$. The polynomial $g$ has degree at most $d+1$ in each variable.

## Proof sketch

Summing $L_j$ over the hypercube gives the multilinear extension of $M_jz_1$ at $r_x$, which equals $v_j$ by the LCCCS relation. Summing $Q$ gives the multilinear extension in $\beta$ of the CCS residual of $z_2$, which is zero iff it is satisfying, and nonzero otherwise except with probability $s/|\mathbb{F}|$. A random $\gamma$ separates the $t+1$ claims except with probability $(t+1)/|\mathbb{F}|$.

## Depends on

- [Linearized committed CCS instances](linearized-committed-ccs.md)
- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)
- [Customizable constraint systems](customizable-constraint-system.md)

## Proof depends on

- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)
- [Zero-check reduction to sum-check via the equality polynomial](../plonkish-polynomial-iops/zerocheck-reduction.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573.
