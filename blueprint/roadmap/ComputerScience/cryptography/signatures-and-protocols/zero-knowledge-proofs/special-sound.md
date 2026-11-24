# Special soundness of a Sigma protocol

A [Sigma protocol](sigma-protocol.md) is specially sound with an extractor if from any two accepting
transcripts $(a, e, z)$ and $(a, e', z')$ for a statement $x$ with the same commitment and different
challenges $e \ne e'$, the extractor computes a witness for $x$.

## Sources

- I. Damgård, *On Σ-protocols*, lecture notes, Aarhus University, 2010.
