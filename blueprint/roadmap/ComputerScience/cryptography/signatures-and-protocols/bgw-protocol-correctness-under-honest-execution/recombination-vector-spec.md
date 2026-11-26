# Recombination weights for Shamir parameters

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` satisfying `2 * params.threshold < Fintype.card Party`.
Then there are weights `lam : Party → F` with `∑ i, lam i * p.eval
(params.point i) = p.eval 0` for every polynomial `p` of natural degree at
most `2 * params.threshold`.
