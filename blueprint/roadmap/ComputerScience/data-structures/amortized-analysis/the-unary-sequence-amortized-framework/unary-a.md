# Unary A

`A f i`: the amortized cost of the `i`-th operation. This is
`PotentialMethod.amortizedCost` specialized to the run `unaryState A f`
with actual costs `A.T (f i) (unaryState A f i)`; the Isabelle name is
retained as a compatibility wrapper.
