# Split-incompatibility formulas for majority-rule supertree distances

**Setting.** Let $S$ be an unrooted bifurcating supertree on a taxon set $X$ and $G$ an unrooted bifurcating input tree on $Y \subseteq X$. Splits are the nontrivial bipartitions induced by inner edges; a bifurcating tree on $n$ taxa has $n-3$ of them. Two splits on overlapping taxon sets are compared by first restricting both to their common taxa; they are *incompatible* if the restrictions cannot occur together in one tree. Three Robinson-Foulds-type distances between a supertree and an input tree on fewer taxa are considered:

- $d^-(S,G)$: the Robinson-Foulds distance between $S|_Y$ (the supertree pruned to $Y$) and $G$;
- $d^+(S,G)$: the minimum Robinson-Foulds distance between $S$ and any bifurcating tree on $X$ obtained from $G$ by grafting the taxa of $X \setminus Y$ onto edges;
- $d^+_g(S,G)$: the same minimum when the missing taxa may be grafted onto edges or onto nodes (so the extended tree may be multifurcating).

Let $C$ be the number of splits of $G$ that are incompatible with at least one split of $S$, and $B$ the number of splits of $S$ that are incompatible with at least one split of $G$. Then $B \ge C$ and

$$d^-(S,G) = 2C, \qquad d^+_g(S,G) = B + C, \qquad d^+(S,G) = 2B.$$

If $G$ is multifurcating and lacks $m$ inner edges relative to a bifurcating tree, then $d^-(S,G) = 2C + m$, and since $m$ does not depend on $S$ the MR(-) objective is unchanged.

**Majority-rule supertrees.** For a profile of input trees, the MR(-), MR(+)g and MR(+) scores of $S$ are the sums of $d^-$, $d^+_g$ and $d^+$ over the inputs. The corresponding majority-rule supertree is the strict consensus of all optimal bifurcating supertrees, contracted by deleting every split contradicted by at least half of the input trees. When all inputs are bifurcating on the same taxon set nothing can be grafted, so all three scores reduce to the summed Robinson-Foulds distance and each method generalizes the majority-rule consensus.

## Depends on

- [Compatible splits](../../../splits-compatibility-ultrametrics-and-upgma/compatible.md)
- [Majority splits of a family of trees](../../../splits-compatibility-ultrametrics-and-upgma/majority-splits.md)
- [Robinson–Foulds distance](../../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

For $d^-$: both $S|_Y$ and $G$ are bifurcating on $Y$, so each split of one is either identical to or incompatible with some split of the other, and a split of $S$ conflicts with $G$ exactly when its restriction to $Y$ does, because incompatibility can only arise from taxa in $Y$; hence the symmetric difference has $2C$ elements. For $d^+_g$ the lower bound $B + C$ is immediate, and a matching extension is built by placing missing taxa one at a time. A taxon is "good" when an input split is a subsplit of two supertree splits that differ only in that taxon, and it can be placed on the edge between them at no cost; counting rows and columns of the input-versus-supertree relationship matrix (entries: subsplit, compatible, incompatible) shows that exactly $B - C$ "bad" taxa remain, each placed on a node adjacent to a conflicting split at cost one, giving $2C + (B - C)$. For $d^+$ the bad taxa must go on edges, each costing two, which gives $2C + 2(B - C) = 2B$. The formulas make each score computable from the relationship matrix in time proportional to the number of split pairs, which is what makes heuristic tree search over supertrees practical.

## Sources

- A. Kupczok, "Split-based computation of majority-rule supertrees", BMC Evolutionary Biology 11:205 (2011), Theorems 1-3 (Methods) and the Results section on the three distances, <https://doi.org/10.1186/1471-2148-11-205>, PMCID PMC3169514.
