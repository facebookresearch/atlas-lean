# Bottleneck conditioning and global Granger causality

**Setting.** Let the nodes $X_1,\dots,X_N$ of a regulatory network evolve by a linear vector autoregression whose nonzero lagged coefficients define a directed interaction graph, and assume no unobserved common drivers. Write $F_{S\to T\mid \mathcal C}$ for the conditional (partial) Granger causality from node $S$ to node $T$ given the set of nodes $\mathcal C$ (see [conditional Granger causality](conditional-granger-causality-of-differenced-series-in-time-and-frequency.md)).

**Definition (section, bottleneck).** A set of nodes $\{Z_1,\dots,Z_m\}$, not containing $S$ or $T$, is a *section* from $S$ to $T$ if deleting it leaves no directed path from $S$ to $T$. A section of minimum cardinality is a *bottleneck*; its size is the vertex connectivity from $S$ to $T$.

**Lemma.** If $\{B_1,\dots,B_m\}$ is a bottleneck from $S$ to $T$, then

$$F_{S \to T \mid B_1,\dots,B_m} = 0 .$$

The paper proves this for a serial chain $S \to B_1 \to \cdots \to B_n \to T$ (where each single $B_i$ is a bottleneck) and for paths that first diverge and then converge on a common bottleneck node.

**Global Granger causality (GGC).** To find the direct parents of a target $T$ when the number of nodes may exceed the length of the time series:
1. Let $A_0(T)$ be the set of nodes with nonzero pairwise Granger causality to $T$ (direct and indirect ancestors).
2. For $j = 1,2,\dots$: delete from $A_{j-1}(T)$ every node $S$ for which $F_{S\to T\mid \mathcal C}$ vanishes for some $\mathcal C \subseteq A_{j-1}(T)\setminus\{S\}$ with $|\mathcal C| = j$; call the result $A_j(T)$.
3. Stop when no node is deleted.

By the lemma, an indirect ancestor whose bottleneck to $T$ has size $m$ and lies inside the current candidate set is removed at stage $m$, while a direct parent, which no section can separate from $T$, is never removed. Each stage conditions on only $j$ nodes, so the regressions stay low-dimensional.

## Expansion

All information from $S$ reaches $T$ through the bottleneck, so once the pasts of the bottleneck nodes are included in the predictor of $T$, the past of $S$ adds nothing; this is the vanishing statement. Conditioning on all other nodes at once would also remove indirect links but is infeasible for short series; stage-wise conditioning on small subsets exploits that in sparse random networks most indirect ancestors have small bottlenecks. The paper reports the empirical distribution of bottleneck sizes in random directed graphs to justify stopping after few stages, and applies the procedure to a five-gene yeast network and to proteomic time series of several hundred proteins.

## Sources

- C. Zou, C. Ladroue, S. Guo, J. Feng, "Identifying interactions in the time and frequency domains in local and global networks - A Granger Causality Approach", BMC Bioinformatics (2010), Methods: global Granger causality (Fig. 1, steps (I)–(III)); Discussion: Definition 1 (bottleneck) and Lemma 1, <https://doi.org/10.1186/1471-2105-11-337>, PMCID PMC2897832.
