# Monotypic alignments make every tree maximum-likelihood optimal

**Jukes–Cantor model trees.** A Jukes–Cantor (JC) model tree $(T,\theta)$ is a rooted binary tree $T$ on a taxon set $S$ with a substitution probability $p(e) \in (0, \tfrac34)$ on each edge; the root state is uniform on $\{A,C,G,T\}$, a change on edge $e$ occurs with probability $p(e)$ and goes to each of the other three states with equal probability, and sites evolve i.i.d. For an alignment $A$ and topology $T$, let

$$\mathrm{ML}_{JC}(A, T) = \sup_\theta P(A \mid T, \theta),$$

where gaps are treated as missing data (summed over all states). The supremum need not be attained because the parameter range is open.

**Monotypic alignment.** An alignment of the sequences in $S$ is *monotypic* if every site contains exactly one nucleotide type among its non-gap entries (and no site is entirely gapped).

**Lemma.** If $A$ is monotypic with $R$ sites and gaps are treated as missing data, then $\mathrm{ML}_{JC}(A,T) = (1/4)^R$ for every tree $T$ on $S$.

**Theorem.** If $A$ is monotypic, then every tree on $S$ is an optimal solution of maximum likelihood under Jukes–Cantor when gaps are treated as missing data.

**Consequence.** For any model of sequence evolution with indels under which monotypic alignments have positive probability, maximum likelihood with gaps as missing data can fail to be statistically consistent, even when given the true alignment.

## Depends on

- [Jukes–Cantor transition probability](../../jukes-cantor-model/jc-prob.md)

## Expansion

At any site of a monotypic alignment, the observed characters all agree, so letting every $p(e) \to 0$ makes the likelihood of the site equal to the root probability $1/4$ of that nucleotide; no setting can do better since the site likelihood is at most the probability of the root state matching the observed nucleotide. Multiplying over $R$ independent sites gives $(1/4)^R$ for every topology, so the likelihood carries no information about $T$. If a process with insertions and deletions can produce, with probability bounded away from zero, alignments that are monotypic after removing gaps (for example when substitution rates are very low but indels frequent), ML returns all trees with that probability, and so cannot converge to the true tree.

## Sources

- T. Warnow, "Standard maximum likelihood analyses of alignments with gaps can be statistically inconsistent", PLoS Currents: Tree of Life (2012), sections on maximum likelihood on gap-free and gapped alignments, Lemma 1 and Theorem 1, <https://doi.org/10.1371/currents.RRN1308>, PMCID PMC3299439.
