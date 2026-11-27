# Divide-and-colour percolation and neutral mutations on Galton–Watson trees

**Bernoulli percolation as neutral mutation.** In Bernoulli bond percolation with parameter $p$ on a rooted tree, each edge is open independently with probability $p$. Reading each closed edge as a neutral mutation to a new allele (infinitely-many-alleles model), the open cluster of the root is the set of individuals carrying the root's allele.

- On the $d$-ary tree $T_d$ ($d \ge 2$), the root cluster is a Bienaymé–Galton–Watson (BGW) tree with offspring law $\mathrm{Bin}(d,p)$, so $p_c(T_d) = 1/d$.
- (Lyons) On an infinite tree with branching number $b$, $p_c = 1/b$; for a BGW tree with offspring mean $m > 1$, conditioned on non-extinction, $p_c = 1/m$ almost surely.

**Divide-and-colour (DaC) percolation as finitely-many-alleles mutation.** Given a tree, perform Bernoulli bond percolation with parameter $p$, then colour each open cluster independently with one of $d$ colours, the cluster of the root receiving its colour and every other cluster choosing colour $c$ with probability $a_c$. With $d$ colours this models neutral mutation to one of finitely many alleles: a closed edge is a mutation event whose new allele may coincide with the parent's. Let $a_\emptyset$ be the probability that a cluster receives the same colour as the root's cluster.

**Proposition.** The connected component of the root's colour containing the root has the law of the Bernoulli root cluster with parameter

$$\widetilde p = 1 - (1-p)(1 - a_\emptyset) = p + (1-p)a_\emptyset,$$

so it is infinite with positive probability iff the Bernoulli root cluster with parameter $\widetilde p$ is (Häggström's criterion, for $d = 2$ colours).

**Theorem.** Let $\mathcal{T}$ be a BGW tree with offspring mean $m > 1$ and $a_\emptyset < 1/m$. Conditionally on non-extinction, the critical parameter for the DaC model to have an infinite monochromatic component of the root's colour is, almost surely,

$$\widetilde p_c^{\mathcal{T}} = \frac{1 - m a_\emptyset}{m(1 - a_\emptyset)} .$$

In the mutation interpretation, an infinite clan sharing the ancestral allele forms exactly when the probability of a child keeping its mother's allele, $p + (1-p)a_\emptyset$, exceeds $1/m$.

## Depends on

- [Labelled Galton–Watson trees and projection to generation counts](../../../../Probability/branching-processes/galton-watson-process/ulam-harris-labelled-galton-watson-trees-and-pro.md)

## Expansion

Along each edge from a vertex of the root's colour, the child has the same colour either because the edge is open (probability $p$) or because it is closed and the new cluster chooses the same colour (probability $(1-p)a_\emptyset$), independently across edges; hence the root-colour component is a Bernoulli cluster with parameter $\widetilde p$. On a BGW tree that cluster is again a BGW tree with mean $m\widetilde p$, which is supercritical iff $\widetilde p > 1/m$; solving $p + (1-p)a_\emptyset = 1/m$ for $p$ gives the threshold.

## Sources

- Airam Blancas, María Clara Fittipaldi and Saraí Hernández-Torres, "Crossing Bridges Between Percolation Models and Bienaymé-Galton-Watson Trees", in *XIV Symposium on Probability and Stochastic Processes*, Progress in Probability, Springer (2025), 103–132, <https://doi.org/10.1007/978-3-031-96118-2_4>. Numbering as in the preprint arXiv:2411.09621v2, <https://arxiv.org/abs/2411.09621v2>: Propositions 4.1, 4.2, 4.4, 4.5, Theorems 4.3, 5.1 and 5.2.
