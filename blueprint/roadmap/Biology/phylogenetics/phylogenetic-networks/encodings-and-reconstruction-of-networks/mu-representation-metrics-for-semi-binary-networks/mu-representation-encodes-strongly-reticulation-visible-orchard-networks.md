# μ-representation encodes strongly reticulation-visible orchard networks

**Setting.** Let $N$ be a rooted $X$-DAG (or phylogenetic network) with root $\rho$, reticulation set $R$ (nodes of in-degree $\ge2$), and μ-vectors $\mu(v)\in\mathbb{Z}_{\ge0}^X$ counting directed paths from $v$ to each leaf; $\mu(N)$ is the multiset of all μ-vectors. A node $v$ is *stable* (for leaf $a$) if every root-to-$a$ path visits $v$; $N$ is *reticulation-visible* if every reticulation is stable. A *bridge-node* is the head of an arc whose removal disconnects the underlying graph. $N$ is **strongly reticulation-visible** if from the child of each reticulation there is a tree-path (a directed path through tree-nodes only) to a bridge-node. Semi-binary, stack-free and orchard networks are as in the companion article.

**In-degree identity.** For every $X$-DAG and every leaf $a\in X$,

$$\mu(\rho)_a=1+\sum_{r\in R}\bigl(\delta^-(r)-1\bigr)\,\mu(r)_a .$$

If $r$ is stable for $a$, then $\mu(v)_a=P_{vr}\,\mu(r)_a$ for every ancestor $v$ of $r$, where $P_{vr}$ is the number of $v$–$r$ paths; hence in two reticulation-visible $X$-DAGs with equal μ-representations, the same reticulation set, and each reticulation stable for a common leaf, all reticulation in-degrees coincide (determined top-down from the highest reticulations).

**Theorem.** If $N_1,N_2$ are strongly reticulation-visible semi-binary networks with $\mu(N_1)=\mu(N_2)$, then $\mu^\ast(N_1)=\mu^\ast(N_2)$ (the in-degrees are recovered). Moreover, if $N_1,N_2$ are semi-binary stack-free networks with $\mu(N_1)=\mu(N_2)$ and $N_1$ is strongly reticulation-visible and orchard, then $N_1\cong N_2$. Hence

$$d_\mu(N_1,N_2)=\bigl|\mu(N_1)\,\triangle\,\mu(N_2)\bigr|$$

is a metric on semi-binary strongly reticulation-visible orchard networks.

## Depends on

- [Modified μ-representation encodes semi-binary stack-free orchard networks](modified-mu-representation-encodes-semi-binary-stack-free-orchard-networks.md)

## Expansion

The in-degree identity follows by induction on the hybridization number $\sum_r(\delta^-(r)-1)$: deleting one incoming arc of a highest reticulation $r_j$ removes exactly $\mu(r_j)_a$ root-to-$a$ paths and lowers its coefficient by one. In general the resulting linear system can have several solutions, but stability supplies one equation per reticulation with all ancestors' in-degrees already known. Orchard networks have no tree-clones, so the reticulations are exactly the μ-vectors of multiplicity $2$. Bridge-nodes are recognizable from $\mu(N)$ alone: a non-unit, non-root vector is a bridge-node vector iff it splits in exactly one way as a sum $\mu(k)+\mu(\ell)$ of two vectors in $\mu(N)$ with a multiplicity condition. From a bridge-node one finds the lowest reticulation above it, which is stable for every leaf below the bridge; strong reticulation-visibility guarantees every reticulation arises this way. This recovers $\mu^\ast(N)$ from $\mu(N)$, and the modified-μ encoding theorem finishes the proof.

## Sources

- Christopher Reichling, Leo van Iersel and Yukihiro Murakami, "Metrics for classes of semi-binary phylogenetic networks using μ-representations", Advances in Applied Mathematics 172 (2026), 102953, <https://doi.org/10.1016/j.aam.2025.102953>; numbering as in arXiv:2412.05107: Section 4: Proposition 1 (in-degree formula), Lemma 4, Proposition 2, Lemma 12, Proposition 3 (bridge-node characterization), Theorems 3 and 4.
