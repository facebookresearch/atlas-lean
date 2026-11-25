# Bm25 Term Score

One BM25 term score under a nonnegative-IDF convention, as a total
real-algebra extension.

`idf` is the already chosen nonnegative inverse-document-frequency weight;
this definition does not use the raw Robertson IDF variant, which can be
negative. `tf` is term frequency and `k1` is the BM25 saturation parameter.
The displayed formula is the BM25 score on the standard domain described in
the module documentation; at parameter values making a denominator zero it
uses Lean's totalized division.
