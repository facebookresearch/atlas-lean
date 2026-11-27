# Universal compressed representations from string attractors

Given a string attractor of size $\gamma'$ for $T[1..n]$ over an alphabet of size $\sigma$, write $\Lambda_\tau = \max\{1, \log_\tau(n/\gamma')\}$, the number of levels saturated below by $1$ so that the terminal level is counted. For every integer $\tau \ge 2$ there is a data structure of $O(\gamma'\tau\Lambda_\tau)$ words of $w$ bits that extracts any substring of length $\ell$ in $O(\Lambda_\tau + \ell\log\sigma/w)$ time; for $\tau = 2$ this is $O(\gamma'\max\{1, \log(n/\gamma')\})$ words and $O(\max\{1, \log(n/\gamma')\} + \ell\log\sigma/w)$ time. Without the saturation the bound would be wrong: the set of all $n$ positions is an attractor, and $\gamma' = n$ would give zero words for every binary string of length $n$. Since every dictionary compressor induces an attractor of size at most its output, this gives a single representation whose size is within an $O(\max\{1, \log(n/\gamma)\})$ factor of the outputs of LZ77, SLPs, macro schemes and run-length BWT.

## Proof sketch

Build a hierarchy of blocks: at level $i$ the text is cut into blocks of length $\Theta(n/(\gamma' 2^{i}))$ around the attractor positions, and every block not containing an attractor position is represented by a pointer to an occurrence of it that crosses one, which lies inside at most two blocks of the next level. A query follows $O(\log(n/\gamma'))$ such pointers down to explicitly stored short blocks.

## Depends on

- [String attractors](string-attractor.md)
- [Size $z$ of the greedy LZ77 factorization](lz77-factorization-size.md)
- [Grammar size $g$ and bidirectional macro scheme size $b$](grammar-and-macro-measures.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](bwt-run-count.md)

## Proof depends on

- [Dictionary compressors induce string attractors](compressors-induce-attractors.md)

## Sources

- Dominik Kempa, Nicola Prezza, "At the Roots of Dictionary Compression: String Attractors", STOC (2018), arXiv:1710.10964, Theorem 5.3.
