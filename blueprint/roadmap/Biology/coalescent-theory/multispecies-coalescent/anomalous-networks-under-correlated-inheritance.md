# Hard and soft anomalous networks under the network multispecies coalescent

Let $\mathcal{N}^+$ be a rooted metric phylogenetic network on taxon set $X$, evolving gene trees under the
network multispecies coalescent with correlated inheritance $\mathrm{NMSC}(\rho)$: within each branch
lineages coalesce as in Kingman's coalescent, and at each reticulation, for each locus, the gene copies
present choose parental lineages by a Dirichlet process whose base distribution is given by the
inheritance probabilities $\gamma(e)$ and whose concentration parameter is $\alpha = (1-\rho)/\rho$. Thus
$\rho = 0$ gives independent parental origins for distinct lineages at a reticulation and $\rho = 1$ gives
a common parental origin. Write $P_\rho(T \mid \mathcal{N}^+)$ for the probability of the unrooted binary
tree topology $T$, and for $Y \subseteq X$ let $\mathcal{N}^+_Y$ be the induced network on $Y$ and
$\gamma(T)$ the total inheritance weight of the displayed trees inducing $T$.

- $\mathcal{N}^+$ is **hard-anomalous**, or simply anomalous, under $\mathrm{NMSC}(\rho)$ if there exist
  $Y \subseteq X$ and unrooted binary topologies $T_1, T_2$ on $Y$ such that $T_1$ is induced by a tree
  displayed in $\mathcal{N}^+_Y$, $T_2$ is induced by no tree displayed in $\mathcal{N}^+_Y$, and
  $P_\rho(T_1 \mid \mathcal{N}^+) < P_\rho(T_2 \mid \mathcal{N}^+)$.
- $\mathcal{N}^+$ is **soft-anomalous** if there exist $Y \subseteq X$ and unrooted binary topologies
  $T_1, T_2$ on $Y$ with $\gamma(T_1) > \gamma(T_2)$ and
  $P_\rho(T_1 \mid \mathcal{N}^+) < P_\rho(T_2 \mid \mathcal{N}^+)$.

Every hard anomaly is a soft anomaly, since a topology is displayed exactly when its inheritance weight is
positive. Call a $4$-taxon binary network of **class $k$** when its displayed trees induce exactly $k$ of
the three unrooted quartet topologies. On four taxa the definition takes the equivalent form: a class-$1$
network $\mathcal{N}$ is anomalous if $P_\rho(T_1 \mid \mathcal{N}) < 1/3$ for its unique displayed
topology $T_1$, and a class-$2$ network is anomalous if
$P_\rho(T_3 \mid \mathcal{N}) > \min\{P_\rho(T_1 \mid \mathcal{N}), P_\rho(T_2 \mid \mathcal{N})\}$,
where $T_3$ is the undisplayed topology. A class-$3$ network can be soft-anomalous but never
hard-anomalous.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [Identifiability of networks under the network multispecies coalescent](network-coalescent-identifiability-questions-spe.md)

## Expansion

The equivalence of the four-taxon form with the general definition rests on the fact that a $4$-taxon
binary network displays a single quartet tree exactly when it has no $4$-blob: without a $4$-blob the
network has a cut edge separating two pairs of taxa, whose split is the only non-trivial split of any
displayed tree, and the three quartet probabilities sum to $1$, so being beaten by an undisplayed topology
is the same as falling below $1/3$. A hard anomaly is the stronger failure mode for inference, because the
most probable gene quartets are then not the ones the network displays.

## Sources

- C. Ané, J. Fogg, E. S. Allman, H. Baños and J. A. Rhodes, "Anomalous networks under the multispecies coalescent: theory and prevalence", Journal of Mathematical Biology 88 (2024), 29, <https://doi.org/10.1007/s00285-024-02050-7>. (Definitions 1 and 2, Lemma 1.)
