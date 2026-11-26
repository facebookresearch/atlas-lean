# The function $\varphi$ on text positions

For a text $T$ with suffix array $\mathrm{SA}$ and inverse suffix array $\mathrm{ISA}$, define $\varphi(i) = \mathrm{SA}[\mathrm{ISA}[i] - 1]$ for every text position $i$ whose suffix is not the lexicographically smallest: $\varphi(i)$ is the starting position of the suffix immediately preceding the suffix starting at $i$ in suffix-array order. Iterating $\varphi$ from $\mathrm{SA}[ep]$ enumerates $\mathrm{SA}[ep], \mathrm{SA}[ep-1], \dots, \mathrm{SA}[sp]$.

## Depends on

- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [Toehold lemma](toehold-lemma.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
