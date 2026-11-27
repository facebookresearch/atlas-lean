# Recombination vector over the Shamir evaluation points

Let `F` be a field and `Party` a finite type, with Shamir parameters `params`.
If `2 * params.threshold < Fintype.card Party`, there is `r : Party → F` such
that every polynomial `p` of natural degree at most `2 * params.threshold`
satisfies `p.eval 0 = ∑ i, r i * p.eval (params.point i)`.
