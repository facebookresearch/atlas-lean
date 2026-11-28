# The r-index locates in BWT-runs bounded space

Every text $T$ of length $n$ over an alphabet of size $\sigma$ with $r$ BWT runs has an index of $O(r)$ words that counts the occurrences of a pattern $P[1..m]$ in $O(m \log\log_w(\sigma + n/r))$ time and reports the positions of all $\mathit{occ}$ occurrences in $O(m \log\log_w(\sigma + n/r) + \mathit{occ} \log\log_w(n/r))$ time. This closes the long-standing problem of locating efficiently within space bounded in terms of $r$.

## Proof sketch

Run backward search with the toehold lemma to obtain the interval and $\mathrm{SA}[ep]$, then apply $\varphi$ repeatedly $\mathit{occ} - 1$ times using the run-sample representation of $\varphi$; each application is one successor query over $O(r)$ positions.

## Depends on

- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)

## Proof depends on

- [FM-index backward search](../burrows-wheeler-transform-and-fm-index/backward-search.md)
- [Toehold lemma](toehold-lemma.md)
- [$\varphi$ is determined by $O(r)$ samples](phi-from-run-samples.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
