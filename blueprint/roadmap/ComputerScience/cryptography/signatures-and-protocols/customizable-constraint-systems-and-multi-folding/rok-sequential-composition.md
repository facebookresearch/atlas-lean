# Sequential composition of reductions of knowledge

If $\Pi_1$ is a reduction of knowledge from $\mathcal{R}_1$ to $\mathcal{R}_2$ and $\Pi_2$ is a reduction of knowledge from $\mathcal{R}_2$ to $\mathcal{R}_3$, then running $\Pi_1$ followed by $\Pi_2$ on its output is a reduction of knowledge from $\mathcal{R}_1$ to $\mathcal{R}_3$; if both are public-coin, so is the composition, and the composed extractor runs in expected polynomial time. Likewise, the parallel composition of reductions from $\mathcal{R}_i$ to $\mathcal{R}'_i$ is a reduction from $\mathcal{R}_1\times\mathcal{R}_2$ to $\mathcal{R}'_1\times\mathcal{R}'_2$. In particular, HyperNova's multi-folding factors as a sum-check reduction from (LCCCS, CCCS) to a pair of LCCCS instances at a common point, followed by a linear-combination reduction to one LCCCS instance.

## Proof sketch

Given a composed prover, public reducibility of $\Pi_1$ computes the intermediate statement $u_2$ from the transcript, so the extractor of $\Pi_2$ can be run on it; it yields an expected polynomial-time prover for $\Pi_1$ outputting valid $\mathcal{R}_2$ witnesses; feeding it to the extractor of $\Pi_1$ gives $\mathcal{R}_1$ witnesses. The success probabilities degrade additively by negligible terms and expected running times multiply, staying polynomial.

## Depends on

- [Reductions of knowledge between relations](reductions-of-knowledge.md)
- [Linearized committed CCS instances](linearized-committed-ccs.md)

## Sources

- Abhiram Kothapalli, Bryan Parno, "Algebraic Reductions of Knowledge", CRYPTO (2023), IACR ePrint 2022/009, Theorem 5.
- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573.
