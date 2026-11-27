# Iterated-logarithmic lower bound for long prime gaps

Let $L_1(X)=\log X$ and $L_{j+1}(X)=\log L_j(X)$, using the natural logarithm for sufficiently large real $X$. Set

$$F(X)=\frac{L_1(X)L_2(X)^2 L_4(X)}{L_3(X)^2}.$$

There is a real $c>0$ such that for every sufficiently large real $X$ there are consecutive primes $p<q$ with $q\le X$ and $cF(X)\le q-p$. The upper prime, not just the lower one, must lie below or at the cutoff. The gap is the natural difference cast to the reals.

Equivalently, after changing $c$ and the cutoff, there exist $c>0$ and $X_0\in\mathbb R$ such that for every $X\ge X_0$ some $n\in\mathbb N$ satisfies $p_{n+1}<X$ and $cF(X)<p_{n+1}-p_n$, with $p_0=2$ and subtraction in the reals. To pass from the weak to the strict version, apply the first version at $X^{1/8}$ and use the eventual lower bound $F(X^{1/8})\ge F(X)/64$ and the positivity of the gap to shrink the constant. The reverse follows by forgetting strictness and taking the consecutive pair.

## Depends on

- [Consecutive primes](are-consecutive-primes.md)

## Proof depends on

- [Short translates avoiding primes](short-translates-avoiding-primes.md)
- [Successive primes in the enumeration are consecutive](consecutive-nth-prime.md)

## Expansion

Decompose the covering argument into the smooth-number cutoff, the prime-residue covering and the remaining sparse set to which the short-translate result applies. Use the Chinese remainder theorem and the prime bracketing construction to get a consecutive pair with both primes within the cutoff. Then check scale comparison, coercions and adjoining-prime indexing for the strict version.

## Sources

- [OpenAI, *Improved Long Gaps Between Primes*, Theorem 1.1 and §3](https://cdn.openai.com/pdf/51126fac-1b68-4128-9666-c908bcc16033/long_gaps.pdf)
- [Endpoint and scale comparison in the formal proof](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4431-L4539)
- [Pinned source: `long_gap_theorem`](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4468-L4468)
- [Pinned source: `long_prime_gaps`](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/Challenge.lean#L6-L12)
- [Pinned source: `long_prime_gaps`](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4502-L4508)
