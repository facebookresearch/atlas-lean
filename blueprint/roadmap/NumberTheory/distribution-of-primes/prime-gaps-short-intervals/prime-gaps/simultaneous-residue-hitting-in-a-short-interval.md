# Simultaneous residue hitting in a short interval

For large real $x$, let $\mathcal P_x$ be the primes in $(\lfloor x^6\rfloor,\lfloor\exp(x/(\log x)^5)\rfloor]$. There is an absolute $0<\delta<1/2$ such that for every sufficiently large $x$, every positive integer $m\le\delta x$ and every choice at each $p\in\mathcal P_x$ of $m$ pairwise distinct residues $r_{p,i}\bmod p$, there is one integer $0\le n<\lfloor e^x\rfloor$ such that for every $i$ at least one $p\in\mathcal P_x$ has $n\equiv r_{p,i}\pmod p$. The prime may depend on $i$; the integer may not. The formal proof takes $\delta$ to be the reciprocal of 64 times its common coefficient bound.

## Proof depends on

- [Coefficient and truncation bounds for a simultaneous-root sieve](truncated-sieve-coefficient-estimates.md)
- [Eventual coefficient estimates for the auxiliary prime product](eventual-coefficient-estimates-for-auxiliary-primes.md)

## Sources

- [Prime cutoffs and modulus](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1666-L1676)
- [Fixed density threshold and simultaneous-root theorem](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3466-L3485)
