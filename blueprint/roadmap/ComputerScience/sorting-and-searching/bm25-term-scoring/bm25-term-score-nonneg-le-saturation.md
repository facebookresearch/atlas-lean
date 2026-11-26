# BM25 term scores are nonnegative and saturate

Let `idf ≥ 0`, `tf ≥ 0`, `k1 > 0`, and let the length-normalization factor `(1
- b) + b * (docLen / avgLen)` be positive. Then the BM25 term score is
nonnegative and at most `idf * (k1 + 1)`.
