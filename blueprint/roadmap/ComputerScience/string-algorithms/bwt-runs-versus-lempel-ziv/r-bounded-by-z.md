# Resolution of the BWT-runs conjecture

For every string $T$ of length $n$ (terminated by a unique smallest symbol \$, as in the definition of $r$), the number of BWT runs satisfies $r(T) = O\big(z(T) \log^2 n\big)$, and in fact $r(T) = O\big(\delta(T) \log^2 n\big)$. In particular $r$, $z$ and $\gamma$ are within polylogarithmic factors of each other.

## Proof sketch

Every BWT run boundary $i$ ($\mathrm{BWT}[i-1] \ne \mathrm{BWT}[i]$) makes $\mathrm{LCP}[i]$ an irreducible LCP value. Kempa and Kociumaka show that for every $\ell$ the number of irreducible LCP values in $[\ell, 2\ell)$ is $O(z\log n)$: each such value is charged $\ell$ units, spread over characters of distinct length-$3\ell$ substrings of the cyclic text, of which there are at most $3\ell z$ since each crosses or starts at an LZ77 phrase boundary, and each substring is charged at most $2\log n$ times. Summing over $O(\log n)$ dyadic ranges gives $r = O(z\log^2 n)$; replacing the count of length-$3\ell$ substrings by $3\ell\delta$ gives $r = O(\delta\log^2 n)$.

## Depends on

- [The BWT-runs conjecture](bwt-runs-conjecture.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)
- [Size $z$ of the greedy LZ77 factorization](../string-attractors-and-repetitiveness-measures/lz77-factorization-size.md)
- [String attractors](../string-attractors-and-repetitiveness-measures/string-attractor.md)

## Proof depends on

- [Substring complexity is at most the attractor size](../string-attractors-and-repetitiveness-measures/delta-at-most-gamma.md)
- [Dictionary compressors induce string attractors](../string-attractors-and-repetitiveness-measures/compressors-induce-attractors.md)
- [Strings are representable in $O(\delta\log(n/\delta))$ space, optimally](../string-attractors-and-repetitiveness-measures/delta-optimal-space.md)

## Sources

- Dominik Kempa, Tomasz Kociumaka, "Resolution of the Burrows-Wheeler Transform Conjecture", FOCS (2020); Communications of the ACM 65(6) (2022), arXiv:1910.10631.
