# Sum-check range proof via a vanishing product

Let $q$ be a prime with $q>2b$, and represent elements of $\mathbb{F}_q=\mathbb{Z}_q$ by centered representatives in $(-q/2,q/2)$, so that $|a|$ is defined for $a\in\mathbb{F}_q$. Then $|a|<b$ iff $P_b(a)=\prod_{j=-(b-1)}^{b-1}(a-j)=0$ in $\mathbb{F}_q$. For a vector $\mathbf{f}\in\mathbb{F}_q^{2^{s}}$ with multilinear extension $\widetilde{f}$, all entries satisfy $|f_i|<b$ iff the function $x\mapsto P_b(\widetilde{f}(x))$ vanishes on $\{0,1\}^{s}$. If it does not vanish, then $\sum_{x\in\{0,1\}^{s}}\widetilde{\mathrm{eq}}(\tau,x)P_b(\widetilde{f}(x))=0$ for a uniformly random $\tau\in\mathbb{F}_q^{s}$ with probability at most $s/q$; the sum is proved by a sum-check of degree at most $2b$ per variable, with soundness error at most $2bs/q$, ending in one evaluation claim about $\widetilde{f}$. Both steps use that $\mathbb{F}_q$ is a field: over $\mathbb{Z}_6$ with $b=2$, $a=2$ one has $(a+1)a(a-1)=0$ although $|a|\not<2$.

## Proof sketch

Since $q$ is prime and $q>2b$, the $2b-1$ values $-(b-1),\dots,b-1$ are distinct elements of the field $\mathbb{F}_q$, which are exactly the elements of absolute value less than $b$, and a product of field elements vanishes iff some factor does. The weighted sum is a multilinear polynomial in $\tau$ whose coefficients on the hypercube basis are the values $P_b(\widetilde{f}(x))$, so it is the zero polynomial iff all of them vanish, and otherwise has at most an $s/q$ fraction of zeros by the Schwartz–Zippel lemma. Sum-check soundness over the field bounds the remaining error.

## Depends on

- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)

## Proof depends on

- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)
- [Zero-check reduction to sum-check via the equality polynomial](../plonkish-polynomial-iops/zerocheck-reduction.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", ASIACRYPT (2025), IACR ePrint 2024/257, Sections 1 and 3 (the range check through the vanishing polynomial over a prime modulus, with coefficients lifted to centered representatives).
