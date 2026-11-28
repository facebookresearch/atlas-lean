# The function $\varphi$ on text positions

For a text $T$ with suffix array $\mathrm{SA}$ and inverse suffix array $\mathrm{ISA}$, define $\varphi(i) = \mathrm{SA}[\mathrm{ISA}[i] - 1]$ if $\mathrm{ISA}[i] > 1$ and $\varphi(i) = \mathrm{SA}[n]$ otherwise, i.e. $\varphi(\mathrm{SA}[1]) = \mathrm{SA}[n]$. For $\mathrm{ISA}[i] > 1$, $\varphi(i)$ is the starting position of the suffix immediately preceding the suffix starting at $i$ in suffix-array order. Thus $\varphi$ maps $\mathrm{SA}[p]$ to $\mathrm{SA}[p-1]$ cyclically, so it is a permutation of the text positions, with inverse $\varphi^{-1}(\mathrm{SA}[p]) = \mathrm{SA}[p+1]$ for $p < n$ and $\varphi^{-1}(\mathrm{SA}[n]) = \mathrm{SA}[1]$. For $1 \le sp \le ep \le n$, iterating $\varphi$ from $\mathrm{SA}[ep]$ enumerates $\mathrm{SA}[ep], \mathrm{SA}[ep-1], \dots, \mathrm{SA}[sp]$.

## Depends on

- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
