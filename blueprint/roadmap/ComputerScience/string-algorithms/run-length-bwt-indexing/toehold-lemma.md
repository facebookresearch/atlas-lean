# Toehold lemma

Store, for every BWT run, the suffix-array values at its first and last rows ($2r$ samples). Then backward search for $P$ can be augmented to output, together with the final interval $[sp, ep]$, the text position $\mathrm{SA}[ep]$ of one occurrence of $P$, with one predecessor query per step, within the backward-search time $O(m \log\log_w(\sigma + n/r))$ on a word RAM with $w$-bit words (Lemma 2).

## Proof sketch

Maintain $q = \mathrm{SA}[ep]$ for the current interval. When extending by $c$: if $\mathrm{BWT}[ep] = c$, the new last row is $\mathrm{LF}(ep)$ and its suffix starts at $q - 1$. Otherwise the new last row is the LF image of the last row $j \le ep$ in $[sp, ep]$ with $\mathrm{BWT}[j] = c$; such a row ends a run of $c$'s, so it is found by one predecessor query $\mathrm{pred}(R_c, ep)$ on the run ends of $c$, and $\mathrm{SA}[j]$ is a stored sample; the new value is $\mathrm{SA}[j] - 1$. If the interval contains no $c$, $P$ does not occur.

## Depends on

- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/bwt.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)
- [FM-index backward search](../burrows-wheeler-transform-and-fm-index/backward-search.md)

## Proof depends on

- [LF-mapping from the last column](../burrows-wheeler-transform-and-fm-index/lf.md)
- [Counting in BWT-runs space](rlfm-counting.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792, Lemma 2.
