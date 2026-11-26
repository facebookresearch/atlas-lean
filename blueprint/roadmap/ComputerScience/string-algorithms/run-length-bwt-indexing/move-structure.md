# Constant-time LF and $\varphi$ steps in $O(r)$ space

For every text with $r$ BWT runs, after splitting the runs into $O(r)$ intervals with a balancing property, the LF-mapping and the $\varphi$ function can each be evaluated in $O(1)$ time per step, given the interval containing the current argument, using $O(r)$ words; consequently, for alphabets of constant size, the occurrences of a pattern $P[1..m]$ can be located in $O(m + \mathit{occ})$ time with an $O(r)$-word index.

## Proof sketch

Nishimoto and Tabei's *move structure* represents a permutation that is piecewise a translation on $O(r)$ input intervals. Splitting intervals so that each output interval overlaps $O(1)$ input intervals guarantees that, after applying the translation, the interval containing the image is found by a constant number of forward scans, so the next step needs no predecessor search; both LF and $\varphi$ are such piecewise translations by the run-sample lemmas.

## Depends on

- [$\varphi$ is determined by $O(r)$ samples](phi-from-run-samples.md)
- [The r-index locates in BWT-runs bounded space](r-index-locate.md)

## Proof depends on

- [$\varphi$ is determined by $O(r)$ samples](phi-from-run-samples.md)
- [The r-index locates in BWT-runs bounded space](r-index-locate.md)

## Sources

- Takaaki Nishimoto, Yasuo Tabei, "Optimal-Time Queries on BWT-Runs Compressed Indexes", ICALP (2021), arXiv:2006.05104.
