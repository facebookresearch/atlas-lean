# Recall At

Recall at cutoff `k` for a ranked prefix `r`.

`rel` is the relevance predicate on the finite candidate universe `Fin N`.
The numerator counts relevant ranked positions and the denominator counts all
relevant candidates. The selected convention when there are no relevant
candidates is `0`. The upper-bound theorem uses the standard ranked-prefix
condition that `r` is injective.
