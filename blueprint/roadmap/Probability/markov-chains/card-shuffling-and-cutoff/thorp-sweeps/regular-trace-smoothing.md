# Uniform regular trace and total-variation smoothing for Thorp sweeps

Use the [physical pair-step, d-step Fourier operator, and Specht model](physical-thorp-step-and-specht-averages.md). Put $N=2^d$ and $\mathcal T_d(P)=\sum_{\mu\vdash N}D_\mu\operatorname{tr}|Q_{d,\mu}|^P$, where $|Q|=(Q^*Q)^{1/2}$. There exists one real $P\ge2$ such that for every $d\ge1$, $\mathcal T_d(P)\le1+N^{-10}$. For each integer $v$ satisfying $P\le2v$ and every deterministic initial permutation, the total-variation distance of the full deck after $vd$ elementary steps to the uniform permutation is at most $N^{-5}/2$.

**Conventions.** Use the exact finite shuffle law on all positions, all Specht degrees including the trivial and sign types, and real powers of a positive absolute-value operator.

## Depends on

- [Tabloid Specht modules and all-copy subgroups on occupied boards](occupied-board-specht-model.md)
- [Physical Thorp pair steps and Specht Fourier averages](physical-thorp-step-and-specht-averages.md)

## Proof depends on

A uniform trace bound at a single real exponent and the regular Fourier formula relating convolution to full-deck $L^2$ distance. The latter uses a singular-value bound on powers of each Fourier block, without assuming the block is self-adjoint.

## Expansion

Establish the regular trace equality and handle the trivial block before subtracting one. Verify the quantitative exponent conversion from the $N^{-10}$ trace excess to $N^{-5}/2$ in total variation. Keep the integer sweep count arbitrary subject to $2v\ge P$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoordinateTrace.lean#L366-L368)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Random-subspace tests and trace smoothing for coordinate sweeps](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Random-subspace-tests-and-trace-smoothing-for-coordinate-sweeps-September-26-2026/paper.pdf)
