# Correctness of the bit-vector algorithm

**Correctness of the bit-vector algorithm** (Myers 1999). For a nonempty pattern `P`, any
text `T` and any threshold `k`, the positions reported by the bit-vector algorithm are, in
increasing order, exactly the text positions `1 ≤ j ≤ |T|` with `dp P T |P| j ≤ k`.

## Sources

- G. Myers, J. ACM 46 (1999) 395-415, the bit-vector column-update algorithm.
