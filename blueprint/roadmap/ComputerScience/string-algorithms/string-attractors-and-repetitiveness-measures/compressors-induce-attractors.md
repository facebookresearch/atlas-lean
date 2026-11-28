# Dictionary compressors induce string attractors

For every string $T$: the set of first positions of the phrases of any bidirectional macro scheme is a string attractor, so $\gamma(T) \le b(T)$; every LZ77 factorization is a bidirectional macro scheme, so $b(T) \le z(T)$; the text positions corresponding to BWT run boundaries form a string attractor, so $\gamma(T) \le r(T)$; and $z(T) \le z_{\mathrm{no}}(T) \le g(T)$, where $z_{\mathrm{no}}$ is the number of phrases of the greedy LZ77 factorization whose phrases may not overlap their earlier occurrences. The first positions include the explicit-symbol positions (the positions of the letter phrases). Navarro states $\gamma \le b$ (Section 3.9), and Kempa and Prezza take both endpoints of every copy phrase together with the explicit-symbol positions, which gives an attractor of size at most $2b$ (Theorem 3.6). Navarro states $z \le z_{\mathrm{no}} \le g$ with the size of a grammar measured as the sum of the lengths of its right-hand sides (Sections 3.2.3 and 3.4); that measure agrees with the SLP rule count $g$ used here up to a constant factor, and the proof sketch gives $z_{\mathrm{no}} \le g$ for the rule count directly.

## Proof sketch

For a macro scheme, any substring either contains a phrase start or lies inside a single copied phrase; following the copy pointer moves the occurrence, and following the finite pointer chain of any one of its positions down to a letter phrase shows that some copy eventually contains a phrase start (a substring that crosses a phrase boundary contains the first position of the later phrase, which is why the first positions, and not only the explicit-symbol positions, are needed). LZ77 phrases copy from the left and terminate trivially. For the BWT, take the text positions whose BWT letter starts a run. Reading an occurrence of a substring right to left by LF steps visits one BWT row per letter; inside a run LF shifts rows by the same offset, so moving the starting row up by the smallest distance from a visited row to the start of its run gives another occurrence of the same substring, and that occurrence visits a run start. The grammar bound is Rytter's: cutting the text at the leftmost occurrences of the nonterminals of an SLP yields a non-overlapping LZ-style parse with at most $g$ phrases, and the greedy parse is no larger.

## Depends on

- [String attractors](string-attractor.md)
- [Grammar size $g$ and bidirectional macro scheme size $b$](grammar-and-macro-measures.md)
- [Size $z$ of the greedy LZ77 factorization](lz77-factorization-size.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](bwt-run-count.md)

## Proof depends on

- [LF-mapping from the last column](../burrows-wheeler-transform-and-fm-index/lf.md)

## Sources

- Dominik Kempa, Nicola Prezza, "At the Roots of Dictionary Compression: String Attractors", STOC (2018), arXiv:1710.10964, Section 2 (bidirectional parses; LZ77 as a particular case), Theorem 3.6, Lemma 3.7 and Theorem 3.9.
- Wojciech Rytter, "Application of Lempel–Ziv Factorization to the Approximation of Grammar-Based Compression", Theoretical Computer Science 302(1-3) (2003).
- Gonzalo Navarro, "Indexing Highly Repetitive String Collections, Part I: Repetitiveness Measures", ACM Computing Surveys 54(2) (2021), arXiv:2004.02781v10, Section 3.2.3 ($z \le z_{\mathrm{no}}$), Section 3.4 (grammar size as the sum of right-hand-side lengths, and $z_{\mathrm{no}} \le g$) and Section 3.9 ($\gamma \le b$).
