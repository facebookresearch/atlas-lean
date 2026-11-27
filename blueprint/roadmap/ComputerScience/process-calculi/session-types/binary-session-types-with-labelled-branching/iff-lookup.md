# Permutation equivalence of well-formed branch lists via lookup

Let the label type have decidable equality, and let `bs` and `cs` be well-formed branch lists (distinct labels and well-formed continuations). Then `bs` and `cs` are permutation-equivalent if and only if their label lists are permutations of each other and, for every label, the lookups of that label in `bs` and in `cs` are either both absent or both present with permutation-equivalent continuations.
