# Effective population size from the family sizes

For a parent map
`parent : Fin (2 * N) → Fin N`, the effective size $N_e$ defined by $P = 1/N_e$, where $P$ is the
probability that two distinct gene copies of the offspring generation come from the same parent
(`sameParentProb`): $N_e = 1/P$, which is $0$ if $P = 0$ (Lean's convention $1/0 = 0$).
