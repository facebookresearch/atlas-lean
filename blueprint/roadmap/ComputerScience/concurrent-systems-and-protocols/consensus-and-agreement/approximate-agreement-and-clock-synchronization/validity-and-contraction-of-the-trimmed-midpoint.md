# Validity and contraction of the trimmed midpoint

For a list $xs$ of $m > 2t$ reals in which at least $m - t$ entries lie in an interval $[lo, hi]$, let $\mathrm{mid}_t(xs)$ be the midpoint of the smallest and largest entries remaining after discarding the $t$ smallest and $t$ largest entries. Then $\mathrm{mid}_t(xs) \in [lo, hi]$. If two such lists share their correct entries (the values of $m - t$ common correct processes, all in $[lo, hi]$) and $m > 3t$, their trimmed midpoints differ by at most $(hi - lo)/2$.

## Proof sketch

After trimming, every remaining entry is bracketed by correct entries, so both extremes lie in $[lo, hi]$. With $m > 3t$, the trimmed ranges of two lists overlap in a correct value, so each midpoint lies in a half of the range adjacent to a common point.

## Depends on

- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- Danny Dolev et al., "Reaching Approximate Agreement in the Presence of Faults", Journal of the ACM, 1986.
