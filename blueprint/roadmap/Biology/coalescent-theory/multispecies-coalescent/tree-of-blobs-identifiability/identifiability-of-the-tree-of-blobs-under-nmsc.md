# Identifiability of the tree of blobs under the network multispecies coalescent

Let $\mathcal{N}^+$ be a rooted binary phylogenetic network on a taxon set $X$ with $|X| = n \ge 4$, under the
network multispecies coalescent (NMSC). Then for generic numerical parameters:

1. Every [B-quartet](blob-and-tree-of-blobs-of-a-phylogenetic-network.md) on $\mathcal{N}^+$ is identifiable from the quartet concordance factors $\{\mathrm{CF}_Q : Q \subseteq X,\, |Q| = 4\}$ by applying [4-blob CF-detectability](cf-detectability-of-4-blobs.md) to all induced 4-taxon networks followed by repeated application of the [B-quartet inference rule](b-quartet-inference-rule.md).
2. Consequently, the reduced unrooted tree of blobs $T_{\mathrm{rd}}(\mathcal{N}^-)$ is uniquely identifiable from the distribution of gene quartet topologies under the NMSC model.

## Depends on

- [Blobs and the reduced unrooted tree of blobs of a phylogenetic network](blob-and-tree-of-blobs-of-a-phylogenetic-network.md)
- [Concordance-factor detectability of 4-blobs on 4-taxon networks](cf-detectability-of-4-blobs.md)
- [B-quartet inference rule on phylogenetic networks](b-quartet-inference-rule.md)

## Expansion

Part 1 is proved by induction on $n$; for $n = 4$ it is the CF-detectability theorem. Two facts are used
throughout: a B-quartet on an induced network on a subset of the taxa is a B-quartet on $\mathcal{N}^+$
(Corollary 2), and if $\{a, b, c, d\}$ is a B-quartet and the network induced on $X \setminus \{\alpha\}$ has a
cut edge separating $a, b$ from $c, d$, then $\{a, b, c, \alpha\}$ is a B-quartet on the network induced on
$X \setminus \{d\}$ (Lemma 3). Let $n \ge 5$ and let $\{a, b, c, d\}$ be a B-quartet, determining a blob $B$.

1. Keep one taxon from each component left by deleting $B$ that contains a taxon (a component may contain
   none, such as the one above the lowest stable ancestor), choosing $a, b, c, d$ as the representatives of
   their components. If this drops a taxon,
   $\{a, b, c, d\}$ is still a B-quartet on the smaller induced network, the inductive hypothesis identifies it
   there, and Corollary 2 lifts it to $\mathcal{N}^+$.
2. Otherwise, if deleting some taxon other than $a, b, c, d$ leaves $\{a, b, c, d\}$ a B-quartet on the induced
   network, conclude in the same way.
3. In the remaining case, fix $\alpha \in X \setminus \{a, b, c, d\}$. On the network induced on
   $X \setminus \{\alpha\}$, $\{a, b, c, d\}$ is a T-quartet, so some cut edge separates two of the taxa, say
   $a, b$, from $c, d$, and the CF-detectability theorem shows $\mathrm{CF}_{abcd}$ is $(ab|cd)$-cut. Lemma 3,
   applied twice, makes $\{a, b, c, \alpha\}$ and $\{b, c, d, \alpha\}$ B-quartets on the networks induced on
   $X \setminus \{d\}$ and $X \setminus \{a\}$; the inductive hypothesis identifies both, Corollary 2 lifts them
   to $\mathcal{N}^+$. These two B-quartets share $\{b, c, \alpha\}$, and on the network induced on
   $\{a, b, c, d\}$ the set is a T-quartet with quartet $ab|cd$, in which $a$ and $d$ are separated. Part (a) of
   the B-quartet inference rule, with $b, c, \alpha$ as the shared taxa, then makes $\{a, b, c, d\}$ a B-quartet.

Part 2: B-quartets are treated as unresolved, and the resolved quartet of each T-quartet is identified from its
concordance factor (Corollary 1), so every quartet displayed on $T_{\mathrm{rd}}(\mathcal{N}^-)$ is identified,
and the displayed quartets determine an unrooted, possibly multifurcating, tree.

## Sources

- E. S. Allman, H. Baños, J. D. Mitchell, and J. A. Rhodes, "The tree of blobs of a species network: identifiability under the coalescent", Journal of Mathematical Biology 86 (2023), 10 (published online 2022), <https://doi.org/10.1007/s00285-022-01838-9> (PMC10062380). (Theorems 3 and 4.)
