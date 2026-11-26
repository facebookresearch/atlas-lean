# Short translates avoiding primes

There is an absolute constant $0\lt \delta<1/2$
such that the following holds for all sufficiently large real $x$. Write
$Q=\prod_{p\le x}p$, over primes $p$. Let $H$ be a natural number with
$x\lt H\le x(\log x)^2$ and let $S\subseteq [1,H]\cap\mathbb N$ with
$|S|\le\delta x$. For each natural number $b\lt Q$ there is a natural number
$1\le t\le e^x$ for which none of the numbers $b+Qt+s$ with $s\in S$ is prime.
Here $Q$ is the primorial of the natural floor of $x$. For large $x$ these
numbers are at least $2$, so nonprimality is equivalent to compositeness.

## Proof depends on

- [Simultaneous residue hitting in a short interval](simultaneous-residue-hitting-in-a-short-interval.md)

## Proof outline

For each auxiliary prime prescribe the roots of the shifted linear forms. They are distinct since the whole interval of shifts is shorter than that prime, and the prime does not divide the primorial. Apply simultaneous residue hitting and set the translate parameter to one plus the common hit. Show every hitting prime is smaller than the corresponding translated integer, so divisibility gives nonprimality. The empty set is handled by the translate parameter one.

## Sources

- OpenAI, [*Improved Long Gaps Between Primes*, Proposition 1.2](https://cdn.openai.com/pdf/51126fac-1b68-4128-9666-c908bcc16033/long_gaps.pdf) and its [formal statement](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L40-L47).
- [Source specialization of the residue hitting theorem](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3612-L3673)
