# Connectivity of transitively closed DAGs under edge moves

**Setting.** Let $\mathcal{T}_n$ be the set of transitively closed directed acyclic graphs on $n$ labelled nodes. For $G\in\mathcal{T}_n$ define two moves (Definition 1):
- $\mathrm{add}(G,i,j)$: for a pair $(i,j)$ that is not an edge of $G$ and whose insertion keeps the graph acyclic, insert $i\to j$ and take the transitive closure;
- $\mathrm{del}(G,i,j)$: for an edge $i\to j$ of the (unique) transitive reduction $G^*$ of $G$, delete it from $G^*$ and take the transitive closure.

Both moves map $\mathcal{T}_n$ to itself.

**Theorem 3.** For any $A,B\in\mathcal{T}_n$, $B$ can be reached from $A$ by a finite sequence of add and del moves. Hence a Markov chain or simulated-annealing search on nested effects network hypotheses that proposes these moves can visit every transitively closed hypothesis.

## Depends on

- [p-value mixture likelihood of a nested effects model](p-value-mixture-likelihood-of-a-nested-effects-model.md)

## Expansion

A DAG has a unique transitive reduction, so del is well defined. An edge of the reduction is not implied by any other path, so after deleting it the closure no longer contains it: each del strictly decreases the edge count, and repeated del moves take $A$ to the empty graph $0$. From $0$, add the edges of $B$ one at a time: each intermediate closure is contained in $B$ (which is closed and contains every inserted edge), so it is acyclic and the next edge of $B$ is either already present or insertable, and after all edges the closure equals $B$. The source phrases the second half through an inverse property of add and del (its Lemma 2), which does not hold in general: from $G=\{k\to i,\ j\to l,\ k\to l\}$, $\mathrm{add}(G,i,j)$ has reduction $k\to i\to j\to l$, and deleting $i\to j$ loses $k\to l$. The theorem itself is unaffected.

## Sources

- H. Fröhlich, M. Fellmann, H. Sültmann, A. Poustka, T. Beißbarth, "Large scale statistical inference of signaling pathways from RNAi and microarray data", BMC Bioinformatics 8 (2007) 386. <https://doi.org/10.1186/1471-2105-8-386>, PMCID PMC2241646. Definition 1, Lemma 2 and Theorem 3.
