# Resolution of the BWT-runs conjecture

For every string $T$ of length $n$, the number of BWT runs satisfies $r(T) = O\big(z(T) \log^2 n\big)$. In particular all three measures $r$, $z$ and $\gamma$ are within polylogarithmic factors of each other.

## Proof sketch

Kempa and Kociumaka bound $r$ via substring complexity: they show that the number of run boundaries in the BWT attributable to substrings of lengths in $[2^i, 2^{i+1})$ is $O(\delta \log n)$ by relating each run boundary to a pair of distinct left extensions of a right-maximal substring and counting right-maximal substrings of a given length range with the help of $d_k \le k\delta$. Summing over $O(\log n)$ length scales gives $r = O(\delta\log^2 n)$, and $\delta \le \gamma \le z$.

## Depends on

- [The BWT-runs conjecture](bwt-runs-conjecture.md)
- [Substring complexity is at most the attractor size](../string-attractors-and-repetitiveness-measures/delta-at-most-gamma.md)
- [Dictionary compressors induce string attractors](../string-attractors-and-repetitiveness-measures/compressors-induce-attractors.md)

## Proof depends on

- [The BWT-runs conjecture](bwt-runs-conjecture.md)
- [Substring complexity is at most the attractor size](../string-attractors-and-repetitiveness-measures/delta-at-most-gamma.md)
- [Dictionary compressors induce string attractors](../string-attractors-and-repetitiveness-measures/compressors-induce-attractors.md)

## Sources

- Dominik Kempa, Tomasz Kociumaka, "Resolution of the Burrows-Wheeler Transform Conjecture", FOCS (2020); Communications of the ACM 65(6) (2022), arXiv:1910.10631.
