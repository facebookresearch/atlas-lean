# Latent-factor Markov networks for gene network inference

Gene networks are often inferred as undirected graphical models, where a missing edge means conditional independence of two genes given all others. Expression data come in different distributions (counts from RNA-seq, discretized or categorical measurements, and others), so the node-conditional models are taken from exponential families, and the network is assembled from estimated node neighbourhoods. Writing every edge weight as a product of shared latent node factors makes the edges symmetric and lets several datasets with different distributions be fused into one network estimate.

- [Latent-factor Poisson neighbourhood regression](latent-factor-poisson-markov-network.md)
- [Collective network inference from heterogeneous data distributions](collective-network-inference-from-heterogeneous-distributions.md)
