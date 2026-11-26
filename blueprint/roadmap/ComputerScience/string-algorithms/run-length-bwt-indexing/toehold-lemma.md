# Toehold lemma

Store, for every BWT run, the suffix-array values at its first and last rows ($2r$ samples). Then backward search for $P$ can be augmented to output, together with the final interval $[sp, ep]$, the text position $\mathrm{SA}[ep]$ of one occurrence of $P$, with $O(1)$ extra work per step.

## Proof sketch

Maintain $q = \mathrm{SA}[ep]$ for the current interval. When extending by $c$: if $\mathrm{BWT}[ep] = c$, the new last row is $\mathrm{LF}(ep)$ and its suffix starts at $q - 1$. Otherwise the new last row is the LF image of the last row $j \le ep$ in $[sp, ep]$ with $\mathrm{BWT}[j] = c$; such a row ends a run of $c$'s, so $\mathrm{SA}[j]$ is a stored sample and the new value is $\mathrm{SA}[j] - 1$. If the interval contains no $c$, $P$ does not occur.

## Depends on

- [Counting in BWT-runs space](rlfm-counting.md)
- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)

## Proof depends on

- [Counting in BWT-runs space](rlfm-counting.md)
- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
