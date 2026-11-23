# Epi

The state of the epidemic at generation `n`: the number of infectives of generation `n`
and the number of contacts made by the earlier generations. Generation `0` is the index case
alone, with no earlier contacts. Generation `n` makes the contacts numbered `D, …, D + c - 1`
with `c = ∑_{i < I} ξ n i`, and the next generation consists of the targets of those contacts
that hit (`epiHit`).
