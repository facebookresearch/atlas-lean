# Bm25 Length Norm

BM25 document-length normalization factor, as a total real-algebra
extension.

With length-normalization parameter `b`, document length `docLen`, and average
document length `avgLen`, this is `(1 - b) + b * docLen / avgLen` on the
standard BM25 domain (`avgLen > 0`, `b ∈ [0, 1]`). Outside that domain the
value is still the displayed totalized real expression, not a BM25 quantity.
