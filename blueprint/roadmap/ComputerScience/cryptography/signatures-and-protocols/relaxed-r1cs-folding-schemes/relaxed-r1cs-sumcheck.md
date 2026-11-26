# Sum-check reduction for relaxed R1CS satisfiability

Let $m=2^{s}$, $n=2^{s'}$, and view $A,B,C$ as functions $\{0,1\}^{s}\times\{0,1\}^{s'}\to\mathbb{F}$ with multilinear extensions $\widetilde{A},\widetilde{B},\widetilde{C}$; let $\widetilde{z}$ and $\widetilde{E}$ be multilinear extensions of $z=(W,u,x)$ and $E$. Define

$$
g(X)=\widetilde{\mathrm{eq}}(\tau,X)\Bigl[\Bigl(\sum_{y}\widetilde{A}(X,y)\widetilde{z}(y)\Bigr)\Bigl(\sum_{y}\widetilde{B}(X,y)\widetilde{z}(y)\Bigr)-u\sum_{y}\widetilde{C}(X,y)\widetilde{z}(y)-\widetilde{E}(X)\Bigr],
$$

sums over $y\in\{0,1\}^{s'}$. If $(E,u,x;W)$ is not satisfying, then for uniformly random $\tau\in\mathbb{F}^{s}$, $\Pr[\sum_{X\in\{0,1\}^{s}}g(X)=0]\le s/|\mathbb{F}|$. Hence a sum-check over $X$ (degree $3$ per variable) followed by a second sum-check over $y$ for the three inner sums reduces relaxed R1CS satisfiability to evaluations of $\widetilde{A},\widetilde{B},\widetilde{C},\widetilde{z},\widetilde{E}$ at random points.

## Proof sketch

The function $q(\tau)=\sum_{X}g(X)$ is the multilinear extension in $\tau$ of the residual vector $Az\circ Bz-uCz-E$, since $\sum_X\widetilde{\mathrm{eq}}(\tau,X)h(X)$ equals the multilinear extension of $h$ at $\tau$. A nonzero residual gives a nonzero multilinear polynomial of total degree at most $s$, which vanishes at random $\tau$ with probability at most $s/|\mathbb{F}|$ by Schwartz–Zippel. Standard sum-check soundness then bounds the error of each round.

## Depends on

- [Relaxed R1CS instances with slack vector and scalar](relaxed-r1cs.md)
- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)

## Proof depends on

- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)
- [Zero-check reduction to sum-check via the equality polynomial](../plonkish-polynomial-iops/zerocheck-reduction.md)

## Sources

- Srinath Setty, "Spartan: Efficient and General-Purpose zkSNARKs without Trusted Setup", CRYPTO (2020), IACR ePrint 2019/550.
- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
