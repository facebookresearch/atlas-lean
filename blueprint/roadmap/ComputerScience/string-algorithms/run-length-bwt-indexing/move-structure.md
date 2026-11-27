# Constant-time LF and $\varphi$ steps in $O(r)$ space

For every text with $r$ BWT runs, after splitting the runs into $O(r)$ intervals with a balancing property, the LF-mapping and the inverse function $\varphi^{-1}$ can each be evaluated in $O(1)$ time per step, given the interval containing the current argument (and returning the interval containing the result), using $O(r)$ words; consequently an $O(r)$-word index counts the occurrences of a pattern $P[1..m]$ over an alphabet of size $\sigma$ in $O(m\log\log_w\sigma)$ time and locates them in $O(m\log\log_w\sigma + \mathit{occ})$ time, which is $O(m + \mathit{occ})$ for $\sigma = \mathrm{polylog}(n)$.

## Proof sketch

Nishimoto and Tabei's *move structure* represents a permutation that is piecewise a translation on $O(r)$ input intervals. Splitting intervals so that each output interval overlaps at most three input intervals guarantees that, after applying the translation, the interval containing the image is found by a constant number of forward scans, so the next step needs no predecessor search; both LF and $\varphi^{-1}$ are such piecewise translations by the run-sample lemmas.

## Depends on

- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)
- [LF-mapping from the last column](../burrows-wheeler-transform-and-fm-index/lf.md)
- [The function $\varphi$ on text positions](phi-function.md)

## Proof depends on

- [$\varphi$ is determined by $O(r)$ samples](phi-from-run-samples.md)
- [The r-index locates in BWT-runs bounded space](r-index-locate.md)

## Sources

- Takaaki Nishimoto, Yasuo Tabei, "Optimal-Time Queries on BWT-Runs Compressed Indexes", ICALP (2021), arXiv:2006.05104.
