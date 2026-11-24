# List Sort Correctness Post

The complete implementation-level functional-correctness certificate.

`rawResultEq` is deliberately part of the public post: the semantic facts are
about the result returned by the transcribed evaluator, not an independently
constructed sorted array.  `entrySnapshot` retains keyed payload pairing in
addition to the key-facing sortedness and stability clauses.
