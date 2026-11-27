# Bottleneck conditioning and global Granger causality

**Setting.** Let the nodes $X_1,\dots,X_N$ of a regulatory network evolve by a linear vector autoregression with mutually independent white-noise innovations, whose nonzero lagged coefficients between distinct nodes define a directed interaction graph. Write $F_{S\to T\mid \mathcal C}$ for the conditional Granger causality from node $S$ to node $T$ given the set of nodes $\mathcal C$ (see [conditional Granger causality](conditional-granger-causality-of-differenced-series-in-time-and-frequency.md)).

**Definition (section, bottleneck).** A set of nodes $\{Z_1,\dots,Z_m\}$, not containing $S$ or $T$, is a *section* from $S$ to $T$ if deleting it leaves no directed path from $S$ to $T$. A section of minimum cardinality is a *bottleneck*; its size is the vertex connectivity from $S$ to $T$.

**Lemma (the configurations the source proves).** Assume, as the source does, that no node other than those on the paths from $S$ to $T$ drives $S$ or $T$: every node lies on a directed path from $S$ to $T$, and the interaction graph has no directed cycles. If either

1. the graph is a serial chain $S \to B_1 \to \cdots \to B_n \to T$ and $B = B_i$ for some $i$, or
2. the paths from $S$ first diverge and then all pass through one common node $B$ before reaching $T$,

then $\{B\}$ is a bottleneck from $S$ to $T$ and

$$F_{S \to T \mid B} = 0 .$$

The hypothesis on drivers cannot be dropped: if an observed node $W$ with autocorrelated dynamics drives both $S$ and $T$ and is not conditioned on, then the past of $S$ carries information about the past of $W$, and $F_{S\to T\mid \mathcal C}$ is in general positive for a bottleneck $\mathcal C$ from $S$ to $T$ that does not contain $W$. The source states the vanishing for a general bottleneck $\{B_1,\dots,B_m\}$ but proves only these two configurations.

**Global Granger causality (GGC).** The procedure below uses conditional Granger causality, a variant of the source's, which computes partial Granger causality (Guo et al. 2008; it also uses the residual covariance of the conditioning variables to remove exogenous and latent inputs). To find the direct parents of a target $T$ when the number of nodes may exceed the length of the time series:

1. Let $A_0(T)$ be the set of nodes with nonzero pairwise Granger causality to $T$ (direct and indirect ancestors).
2. For $j = 1,2,\dots$: delete from $A_{j-1}(T)$ every node $S$ for which $F_{S\to T\mid \mathcal C}$ vanishes for some $\mathcal C \subseteq A_{j-1}(T)\setminus\{S\}$ with $|\mathcal C| = j$; call the result $A_j(T)$.
3. Stop when no node is deleted.

The procedure assumes that conditioning on a bottleneck removes an indirect ancestor, as the lemma shows in its two configurations: an indirect ancestor whose bottleneck to $T$ has size $m$ and lies inside the current candidate set is then removed at stage $m$, while a direct parent, which no section can separate from $T$, is generically never removed (exact cancellations can hide it: for $T_t = aS_{t-2} + bU_{t-1} + e_T$ and $U_t = cS_{t-1} + e_U$ with $a = -bc$, $T$ is independent of $S$ and the direct parent $S$ never enters $A_0(T)$). Each stage conditions on only $j$ nodes, so the regressions stay low-dimensional.

## Expansion

In both configurations let $D$ be the set of nodes with a directed path to $T$ that avoids $B$; it contains $T$ but not $S$. A parent of a node of $D$ lies in $D$ or is $B$, and no node of $D$ is an ancestor of $B$ or of any node outside $D$ (such a node would lie on a cycle through $B$, since every path from $S$ to it passes through $B$). So the processes of $D$, $T$ among them, are linear functions of the past of $B$ and of the innovations of $D$, which are uncorrelated with the processes outside $D$. Once the past of $B$ is in the predictor of $T$, the past of $S$ adds nothing; this is the vanishing statement. Conditioning on all other nodes at once would also remove indirect links but is infeasible for short series; stage-wise conditioning on small subsets exploits that in sparse random networks most indirect ancestors have small bottlenecks. The paper reports the empirical distribution of bottleneck sizes in random directed graphs to justify stopping after few stages; it applies conditional Granger causality to a five-gene yeast network, and the global procedure to synthetic networks and to proteomic time series of 812 proteins.

## Depends on

- [Conditional Granger causality of differenced series in time and frequency](conditional-granger-causality-of-differenced-series-in-time-and-frequency.md)

## Sources

- C. Zou, C. Ladroue, S. Guo, J. Feng, "Identifying interactions in the time and frequency domains in local and global networks - A Granger Causality Approach", BMC Bioinformatics (2010), Methods: global Granger causality (Fig. 1, steps (I)–(III)); Discussion: Definition 1 (bottleneck) and Lemma 1, <https://doi.org/10.1186/1471-2105-11-337>, PMCID PMC2897832.
