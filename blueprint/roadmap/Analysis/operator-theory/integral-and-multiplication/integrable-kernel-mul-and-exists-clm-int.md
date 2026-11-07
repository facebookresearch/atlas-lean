# Integral operators with an $L^p$ kernel map $L^q$ to $L^p$

Let $1 < p < \infty$ and let
$q \ge 1$ be the dual exponent, $p^{-1} + q^{-1} = 1$. Let $K : \mathbb{R}^2 \to \mathbb{R}$ lie
in $L^p((0,1)^2)$, where $L^p((0,1)^2)$, $L^p(0,1)$ and $L^q(0,1)$ are spaces of real functions
for Lebesgue measure. Then for every $f \in L^q(0,1)$ the function $y \mapsto K(x,y)f(y)$ is
integrable on $(0,1)$ for almost every $x \in (0,1)$, and there is a bounded linear operator
$A : L^q(0,1) \to L^p(0,1)$ such that for every $f \in L^q(0,1)$,

$$(Af)(x) = \int_0^1 K(x,y) f(y)\,dy \quad \text{for almost every } x \in (0,1).$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral, integro-differential, and pseudodifferential operators), `benchmark/level2/ma_proofbench_l2_87.lean` at openbmb/ma-proofbench@31bab4c.
