# Zero-check reduction to sum-check via the equality polynomial

Let $g:\{0,1\}^{s}\to\mathbb{F}$ and let $q(\tau)=\sum_{b\in\{0,1\}^{s}}\widetilde{\mathrm{eq}}(\tau,b)g(b)$. Then $q$ is the multilinear extension of $g$, so $q\equiv 0$ iff $g\equiv 0$ on $\{0,1\}^{s}$. If $g$ is not identically zero on the hypercube, then for $\tau$ uniform in $\mathbb{F}^{s}$, $\Pr[q(\tau)=0]\le s/|\mathbb{F}|$. Hence the claim "$g$ vanishes on the hypercube" reduces, with soundness loss $s/|\mathbb{F}|$, to the sum-check claim $\sum_b\widetilde{\mathrm{eq}}(\tau,b)G(b)=0$ for any low-degree extension $G$ of $g$, at the cost of raising the per-variable degree by one.

## Proof sketch

By the defining property of $\widetilde{\mathrm{eq}}$, $q$ agrees with $g$ on the hypercube and is multilinear, hence is its unique multilinear extension. A nonzero multilinear polynomial in $s$ variables has total degree at most $s$, and Schwartz–Zippel bounds its probability of vanishing at a random point by $s/|\mathbb{F}|$.

## Depends on

- [The multilinear equality polynomial on the Boolean hypercube](eq-polynomial.md)
- [Multilinear extension of a Boolean function](../../../../TheoryOfComputation/hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Proof depends on

- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)

## Sources

- Srinath Setty, "Spartan: Efficient and General-Purpose zkSNARKs without Trusted Setup", CRYPTO (2020), IACR ePrint 2019/550.
- Binyi Chen, Benedikt Bünz, Dan Boneh, Zhenfei Zhang, "HyperPlonk: Plonk with Linear-Time Prover and High-Degree Custom Gates", EUROCRYPT (2023), IACR ePrint 2022/1355.
