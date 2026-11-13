# Coalescence along one branch of the species tree

One population of the multispecies coalescent along a branch of length `t`. It receives
`m` lineages `bs` (and the clusters `acc` formed below it). Under Kingman's coalescent the
number `j` of lineages left at the top of the branch has law `tavareProb m j t` (Tavaré's
formula, `exp_blockCountingGenerator_apply`), and, independently of the coalescence times, the
order of the `m - j` coalescences is the beginning of a random-joining history of the `m`
lineages (`randomJoining`). The continuation `k` receives the number of exiting lineages, the
lineages, and the clusters formed so far.
