# Uniform sampling of matching databases

Fix a nonempty finite domain and finitely many
named relations of positive, possibly different arities. Choose a uniform domain permutation
independently for every non-first column of each relation. Form the rows by applying all the
permutations of a relation to its first-column index. The resulting distribution is uniform on
all matching databases of this schema.

## Sources

- Derived sampler for the uniform input law specified in Beame, Koutris and Suciu, *Communication Steps for Parallel Query Processing* (PODS 2013), §2.5, “Input Distribution”.
