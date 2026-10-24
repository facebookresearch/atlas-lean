---
article_id: af_585894d4c9570ceb63325dcb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.mean_short_chords_in_linear_k_chord_diagrams
---

# Mean Short Chords

The mean number of short chords in a linear `k`-chord diagram of length `k * n`.

The left side is the mean (sum of short-chord counts over all diagrams divided
by the number of diagrams); there are `k * n - (k - 1)` consecutive `k`-sets.
This is the mean theorem, distinct from the same paper's asymptotic Poisson
distribution of short chords.
Proves `Wanted` entry `mean_short_chords_in_linear_k_chord_diagrams`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.MeanShortChords](../../../../sources/v2/MathlibExt.md)
- Donovan Young, "Linear k-Chord Diagrams," Journal of Integer Sequences 23 (2020), Article 20.9.1, Theorem (label Thmmean), lines 208–214, https://cs.uwaterloo.ca/journals/JIS/VOL23/Young/young5.tex
