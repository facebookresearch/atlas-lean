# A single recombination vector makes BGW correct

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` satisfying `2 * params.threshold < Fintype.card Party`.
Then there are weights `lam : Party → F` such that for every circuit over the
arithmetic signature, input, input and multiplication randomness, and output
`j`, Shamir reconstruction from all parties' output shares equals the
circuit's output `j`.
