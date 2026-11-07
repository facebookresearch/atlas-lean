# All alignments of sequences over two alphabets

All alignments of a sequence over `α` with a sequence over `β`: lists of columns
`Option α × Option β` with no `(none, none)` column whose rows filter to `xs` and `ys`
(`mem_alignmentsOf`), each listed once (`nodup_alignmentsOf`). For `β = α` this is
`Cslib.Algorithms.Lean.alignments` (`alignmentsOf_eq_alignments`).
