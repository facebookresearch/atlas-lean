# Fuel-bounded enumeration of two-alphabet alignments

All alignments of `xs : List α` with `ys : List β`, by fuel recursion on the first column
(the same recursion as `Cslib.Algorithms.Lean.alignmentsAux`, for two alphabets). Implementation
detail: use `alignmentsOf`, whose fuel `xs.length + ys.length + 1` is enough.
