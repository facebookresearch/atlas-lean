# Hierarchical orthologous groups as components of the orthology graph

Let $\mathcal F$ be a forest of rooted gene trees whose internal nodes are labelled *speciation* or *duplication*, whose leaves are distinct present-day genes, each gene lying in exactly one tree. Two genes are **orthologous** (in Fitch's sense) if their last common ancestral gene is a speciation node. Let $R$ be a taxonomic range, a monophyletic set of species in the species tree, and $\Gamma_R$ the present-day genes of species in $R$. Let $N_R$ be the minimal set of speciation nodes whose descendant leaf sets jointly contain the genes of $\Gamma_R$ without containing genes from species outside $R$ (in the absence of losses: the ancestral genes in the last common ancestor of $R$). For $s \in N_R$, the leaf set $\mathcal L(s)$ is a **hierarchical orthologous group** (HOG) for $R$.

The **orthology graph** has present-day genes as vertices and an edge for every orthologous pair; $O_R$ is its subgraph induced by $\Gamma_R$ (singletons removed).

**Proposition.** The maps between $N_R$, the subtrees rooted at $N_R$, and the HOGs for $R$ are bijections. Two genes in distinct HOGs for $R$ are not orthologous.

**Lemma 1 (components).** For every taxonomic range $R$, the HOGs for $R$ are in one-to-one correspondence with the connected components of $O_R$, and each HOG is the vertex set of its component.

**Lemma 2 (diameter).** On error-free orthology data, every connected component of $O_R$ has diameter at most $2$.

## Expansion

The root of each HOG's subtree is a speciation node, so the genes below its two children are pairwise orthologous: they form a complete bipartite subgraph of $O_R$, which is connected and has diameter at most $2$. Distinct HOGs cannot be joined, because an orthology edge between them would require a speciation node inside $R$ ancestral to both roots, contradicting minimality of $N_R$. This yields an algorithm that traverses the species tree from the leaves and, at each ancestral range, returns the connected components of the induced orthology graph; on noisy pairwise orthology predictions, components whose fraction of vertex pairs reachable in two steps is low are split by minimum cut, using the diameter-two property as the stopping criterion.

## Sources

- A. M. Altenhoff, M. Gil, G. H. Gonnet, C. Dessimoz, "Inferring hierarchical orthologous groups from orthologous gene pairs", PLoS ONE 8(1) (2013) e53786, Methods, Propositions 2–3, Lemmas 1–2, <https://doi.org/10.1371/journal.pone.0053786>, PMCID PMC3544860.
