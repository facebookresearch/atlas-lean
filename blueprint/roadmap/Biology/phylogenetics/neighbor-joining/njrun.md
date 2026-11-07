# Runs of neighbor joining

`NJRun d S D C`: some run of neighbor joining on the dissimilarity `d` reaches the cluster
set `S` with cluster dissimilarity `D`, having formed the clusters in `C`. A join is allowed
while at least four clusters remain, for any pair of distinct clusters minimizing
`qCriterion`.
