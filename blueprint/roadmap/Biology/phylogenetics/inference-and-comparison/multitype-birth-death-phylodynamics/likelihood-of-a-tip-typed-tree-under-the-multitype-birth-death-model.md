# Likelihood of a tip-typed tree under the multitype birth–death model

**Setting.** Consider the [multitype birth–death process](multitype-birth-death-process-and-its-extinction-probabilities.md) with no-sample probabilities $p_{i,k}(t)$. Let $\mathcal T$ be a time-scaled sampled tree whose tips carry their types (a *tip-typed* tree); internal branches have unobserved types.

**Subtree densities.** For a branch $e$ and $t \in [t_{k-1}, t_k)$ along it, let $g^e_{i,k}(t)$ be the probability density that an individual of type $i$ at time $t$ evolved between $t$ and $T$ as the subtree below $e$. It solves the backward master equation

$$-\frac{d}{dt}\,g^e_{i,k}(t) = -\Big(\sum_{j}(\lambda_{ij,k} + m_{ij}) + \mu_{i,k} + \psi_{i,k}\Big) g^e_{i,k}(t) + \sum_{j} m_{ij}\, g^e_{j,k}(t) + \sum_{j}\lambda_{ij,k}\, p_{j,k}(t)\, g^e_{i,k}(t) + \sum_j \lambda_{ij,k}\, p_{i,k}(t)\, g^e_{j,k}(t),$$

with initial value at the lower end $t_e$ of the branch

$$g^e_{i,k}(t_e) = \begin{cases} \psi_{i,k}\big(r + (1 - r)\,p_{i,k}(t_e)\big) & e \text{ a serially sampled tip},\\ \psi_{i,k}(1 - r)\, g^{e_1}_{i,k}(t_e) & e \text{ a sampled ancestor with descendant branch } e_1,\\ \rho_i & e \text{ a tip sampled at the present},\\ \sum_j \lambda_{ij,k}\big[g^{e_1}_{i,k}(t_e)\,g^{e_2}_{j,k}(t_e) + g^{e_1}_{j,k}(t_e)\,g^{e_2}_{i,k}(t_e)\big] & e \text{ splits into } e_1, e_2.\end{cases}$$

The two last terms of the ODE account for a transmission event along the branch whose offspring (or whose parent lineage) left no sampled descendants.

**Tree density.** With $h_i$ the probability that the individual at the origin has type $i$,

$$f(\mathcal T \mid \lambda, \mu, \psi, m, r) = \sum_{i=1}^{d} h_i\, g^{\mathrm{root}}_{i,0}(0).$$

The root-type probabilities can be fixed (for example $h_i = 1/d$) or estimated; equilibrium frequencies are only appropriate when rates are constant in time.

**Multitype (fully typed) trees.** If branch types and type-change times are sampled jointly with the parameters, the type process is not integrated out. Along a branch of known type $i$ the density then solves

$$-\frac{d}{dt}\,g^e_{i,k}(t) = -\Big(\sum_{j}(\lambda_{ij,k} + m_{ij}) + \mu_{i,k} + \psi_{i,k}\Big) g^e_{i,k}(t) + \sum_{j} \eta_{ij}\,\lambda_{ij,k}\, p_{j,k}(t)\, g^e_{i,k}(t),$$

with $\eta_{ij} = 1$ for $i \ne j$ and a doubled weight for $i = j$, where either of the two type-$i$ lineages can be the one that continues the observed branch. A type-change node from $i$ to $j$ (descendant branch $e_1$ of type $j$) has initial value $m_{ij}\, g^{e_1}_{j,k}(t_e) + \lambda_{ij,k}\, g^{e_1}_{j,k}(t_e)\, p_{i,k}(t_e)$, and a split into branches $e_1$ of type $i$ and $e_2$ of type $j$ has initial value $\lambda_{ij,k}\, g^{e_1}_{i,k}(t_e)\, g^{e_2}_{j,k}(t_e)$; tips are as above.

## Depends on

- [Multitype birth–death process and its extinction probabilities](multitype-birth-death-process-and-its-extinction-probabilities.md)
- [Felsenstein's pruning algorithm](../../felsenstein-s-pruning-algorithm/README.md)

## Expansion

The equation for $g$ is again a first-step analysis backward in time over $\Delta t$: either nothing happens; or the lineage changes type; or a transmission occurs with one of the two resulting lineages producing the observed subtree and the other producing no samples (probability $p$), in either order of which lineage survives. At a branching node the two daughter subtrees are conditionally independent given the parent type and the type of the newly infected individual, which gives the product initial condition. A serially sampled tip either is removed (probability $r$) or remains infectious but leaves no further samples ($(1 - r)p$). The recursion is computed from the tips to the root, exactly like pruning on a tree, with the sum over unobserved internal types carried inside the vector $(g_{1,k}, \dots, g_{d,k})$. In the source the model was implemented in a Bayesian MCMC framework and validated against direct stochastic simulation; it was applied to influenza H3N2 across three locations (type changes only) and to HIV transmission between risk groups (between-type births, no type changes).

## Sources

- D. Kühnert, T. Stadler, T. G. Vaughan, A. J. Drummond, "Phylodynamics with migration: a computational framework to quantify population structure from genomic data", Molecular Biology and Evolution (2016), New Approaches ("The Probability Density g that an Individual Evolved as Observed in the Tree", Eq. (1); "The Probability Density f of a Tree"; "Inference of Multitype Trees"), <https://doi.org/10.1093/molbev/msw064> (PMC4948704).
