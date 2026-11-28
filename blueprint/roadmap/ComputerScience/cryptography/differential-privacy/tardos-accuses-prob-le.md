# Tardos Accuses prob le

Exponential-moment bound on the probability that the Tardos rule accuses
user `i` on a fixed word `y` with threshold `Z`, when the codebook is drawn
from `biasCodebookPMF p`, `0 ≤ α` and every bias is at least `α² / 3`: the
probability is at most `(1 + α²) ^ m * exp (-α Z)`, where `m` counts the ones
of `y`. This generalizes the Markov step in Tardos 2008, Section 3 (proof of
Theorem 1), which fixes `α = 1 / (10 c)` before applying Markov's inequality. The word `y` does not depend on the codebook, which models an
innocent user whose row the pirates never see.
