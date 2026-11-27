# Edmonds–Karp terminates within $(n^3 - n)/4$ augmentations

If $s \ne t$, then among the first $(n^3 - n)/4 + 1$ iterates of the Edmonds–Karp [step](step.md) from any integer matrix on $n$ vertices (not necessarily skew-symmetric or feasible), there is one whose residual graph has no path from $s$ to $t$; from then on the step changes nothing. The bound depends on $n$ only, not on the capacities, in contrast with the bound of one more round than the total capacity leaving the source that the [algorithm's fuel](edmonds-karp.md) uses.

## Informally uses

- [Edmonds–Karp augmentation bound (Edmonds and Karp, Theorem 1)](four-mul-le-of-reachable.md)

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 1–3, Lemmas 1 and 2, Theorem 1).
