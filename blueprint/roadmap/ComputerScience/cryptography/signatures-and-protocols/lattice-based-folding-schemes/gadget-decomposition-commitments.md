# Base-b decomposition commutes with Ajtai commitments

For odd $b\ge 3$ and $w\in R_q^{m}$ with $\|w\|_\infty< b^{k}/2$, there are unique $w_0,\dots,w_{k-1}\in R^{m}$ with balanced coefficients, $\|w_i\|_\infty\le (b-1)/2$, and $w=\sum_{i=0}^{k-1}b^{i}w_i$. For a linear commitment $\mathsf{Com}(w)=Aw$ this gives $\mathsf{Com}(w)=\sum_ib^{i}\mathsf{Com}(w_i)$, so a verifier holding $\mathsf{Com}(w)$ and the claimed $\mathsf{Com}(w_i)$ checks consistency with $k$ ring scalar multiplications. Decomposition replaces one large-norm instance by $k$ small-norm instances whose linear claims (evaluations of multilinear extensions) recombine with the same powers of $b$.

## Proof sketch

Balanced base-$b$ digit expansion of each integer coefficient in $(-b^{k}/2,b^{k}/2)$ exists and is unique; apply it coefficientwise. Linearity of $A$ and of multilinear extensions gives the recombination identities.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Proof depends on

- [Relaxed binding of Ajtai commitments with challenge-difference openings](ajtai-relaxed-binding.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", ASIACRYPT (2025), IACR ePrint 2024/257.
