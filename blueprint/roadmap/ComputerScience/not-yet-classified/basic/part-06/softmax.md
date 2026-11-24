# Softmax

Softmax over a finite index set: the shared `Real.softmax` API.

If the index set is empty this uses Lean's totalized division; the
normalization theorem below is stated for a nonempty index set.
