# Exists len ne f4 eq of weight const

Root-stem non-identifiability, existence form: if an edge `e0` has the
same weight for every population (on a rooted tree, an edge of the root stem
above the most recent common ancestor of all sampled populations), then for
every nonnegative `t ≠ len e0` there is a realized drift model with the same
weights, with length `t` at `e0`, hence with a different length vector, but
with every `f4` (hence every `f2` and `f3`) unchanged. So root-stem lengths
are not identifiable from f-statistics. This is the existential form of
`DriftModel.f4_eq_of_len_eq_of_weight_const`, realized by
`Admixture.exists_driftModel`.
