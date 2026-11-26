# Constant-term extraction of exponents in the negacyclic ring

Let $d$ be a power of two and in $\mathbb{Z}_q[X]/(X^{d}+1)$ define

$$
\psi=\sum_{i=1}^{d/2-1}i\cdot\bigl(X^{-i}-X^{i}\bigr).
$$

For every integer $a$ with $|a|< d/2$, the constant term of $X^{a}\cdot\psi$ equals $a$ (where $X^{-i}=-X^{d-i}$). Hence an integer $a$ in this range is encoded by the monomial $X^{a}$, and its value is recovered linearly as $\mathrm{ct}(X^{a}\psi)$; proving that a committed ring element is a monomial therefore certifies a range constraint $|a|< d/2$ without bit decomposition.

## Proof sketch

For $0\le a< d/2$, the product $X^{a}\cdot iX^{-i}$ contributes to the constant term only when $i=a$, contributing $a$, while $-iX^{a+i}$ has $0< a+i< d$ and so never reaches the constant term. For $-d/2< a<0$, the term $-iX^{a+i}$ hits the constant term exactly when $i=-a$, contributing $a$, and $X^{a-i}$ has exponent in $(-d,0)$, i.e., $-X^{d+a-i}$ with $0< d+a-i< d$, contributing nothing. For $a=0$ the constant term is $0$.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems", CRYPTO (2025), IACR ePrint 2025/247.
