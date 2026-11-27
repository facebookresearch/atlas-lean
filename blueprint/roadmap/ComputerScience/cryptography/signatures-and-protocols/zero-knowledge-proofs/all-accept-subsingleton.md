# At most one accepted challenge sequence

Let a Sigma protocol be specially sound, and let $x$ be a statement with no witness. Then for every
$m$ and every adaptive prover, two challenge sequences of length $m$ that are both
[accepted in all rounds](all-accept.md) are equal. In the first round both challenges are answered
for the same commitment, and two accepting transcripts with different challenges would give a witness;
the remaining rounds follow by induction.

## Sources

- I. Damgård, *On Σ-protocols*, lecture notes, Aarhus University, 2010 (special soundness).
