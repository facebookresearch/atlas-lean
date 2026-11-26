# Sum-check range proof via a vanishing product

An integer $a$ satisfies $|a|< b$ iff $P_b(a)=\prod_{j=-(b-1)}^{b-1}(a-j)=0$. For a vector $\mathbf{f}\in\mathbb{Z}_q^{2^{s}}$ of coefficients with $q>2b$, all entries satisfy $|f_i|< b$ iff the function $i\mapsto P_b(f_i)$ vanishes on $\{0,1\}^{s}$; by the zero-check reduction this holds, except with probability $s/q$, iff $\sum_{x\in\{0,1\}^{s}}\widetilde{\mathrm{eq}}(\tau,x)P_b(\widetilde{f}(x))=0$ for random $\tau$, which is proved by a sum-check of degree $2b$ per variable ending in one evaluation claim about $\widetilde{f}$.

## Proof sketch

The polynomial $P_b$ has exactly the roots $-(b-1),\dots,b-1$ in $\mathbb{Z}_q$ when $q>2b$, as these are distinct residues. Apply the zero-check lemma to the function $P_b\circ f$ on the hypercube and run sum-check on its $\widetilde{\mathrm{eq}}$-weighted sum.

## Depends on

- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)

## Proof depends on

- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)
- [Zero-check reduction to sum-check via the equality polynomial](../plonkish-polynomial-iops/zerocheck-reduction.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", IACR ePrint 2024/257 (2024).
