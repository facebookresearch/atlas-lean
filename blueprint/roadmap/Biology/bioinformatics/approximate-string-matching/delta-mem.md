# Deltas lie in `{-1, 0, 1}`

**Deltas lie in `{-1, 0, 1}`** (Myers 1999, Lemma 1). For a pattern `P` and a text `T`, every
vertical delta `dp P T (i+1) j - dp P T i j` with `i < |P|` and `j ≤ |T|`, and every horizontal
delta `dp P T i (j+1) - dp P T i j` with `i ≤ |P|` and `j < |T|`, is `-1`, `0` or `1`.

## Sources

- G. Myers, J. ACM 46 (1999) 395-415, Lemma 1.
- J. Kärkkäinen, *String Processing Algorithms*, lecture notes, University of Helsinki, Autumn 2016, lecture 7, Lemma 3.15, <https://www.cs.helsinki.fi/u/tpkarkka/teach/16-17/SPA/lecture07.pdf>.
