# Fano

Fano's inequality (finite form): for distributions `P i` on a
finite type, an estimator `est`, at least two hypotheses, and
pairwise KL divergences (Mathlib's `klDiv` on the PMFs' measures,
in nats via `toReal`) at most `β`, the average error probability
of `est` is at least `1 - (β + log 2) / log M`.
