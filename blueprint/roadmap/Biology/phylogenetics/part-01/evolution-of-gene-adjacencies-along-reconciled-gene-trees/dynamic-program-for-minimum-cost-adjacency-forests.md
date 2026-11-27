# Dynamic program for minimum-cost adjacency forests

**Setting.** A binary species tree $T_S$ and gene trees reconciled with it by the LCA reconciliation (internal nodes labelled speciation or gene duplication, losses as leaves, each node $N$ assigned a species $S(N)$) are given, together with the extant **adjacencies**: pairs of genes consecutive on a chromosome of an extant genome. An **adjacency tree** follows a pair of gene-tree nodes $(X, Y)$ with $S(X) = S(Y)$ through speciations, joint (adjacency) or single gene duplications, gene or adjacency losses and **breakages** (loss of the adjacency by a rearrangement), starting from one **gain**. An **adjacency forest** is a set of adjacency trees covering every extant adjacency exactly once; its cost is $C(\mathrm{Gain})\cdot\#\text{gains} + C(\mathrm{Break})\cdot\#\text{breaks}$, where a gain is free when it coincides with a tandem duplication or with the roots of the gene trees.

**Decomposition.** Extant adjacencies are partitioned by an equivalence relation (extremities in the same pair of gene trees under nodes of a common species, or below the same duplication when both lie in one tree); adjacencies in different classes cannot belong to one adjacency tree, so each class is solved separately as a problem on two gene trees $T_1$, $T_2$ whose roots have the same species.

**Theorem.** For every pair $(v_1, v_2) \in V(T_1) \times V(T_2)$ with $S(v_1) = S(v_2)$ define
- $c_1(v_1, v_2)$: the minimum cost of an adjacency forest for the adjacencies between $T_1(v_1)$ and $T_2(v_2)$ that contains a node labelled $v_1v_2$ (the ancestral adjacency exists);
- $c_0(v_1, v_2)$: the same minimum over forests with no such node.

Then the minimum cost of an adjacency forest is $\min\{c_1(R_1, R_2), c_0(R_1, R_2)\}$, and $c_0, c_1$ satisfy a recurrence over the event types of $(v_1, v_2)$, evaluated in post-order on pairs of nodes. Base cases: two extant genes give $(c_1, c_0) = (0, \infty)$ if they form an adjacency and $(\infty, 0)$ otherwise; if either node is a gene loss, $c_1 = c_0 = 0$. For a pair of speciation nodes whose children are matched by species, $(a_1, a_2)$ and $(b_1, b_2)$,

$$c_1(v_1, v_2) = \sum_{u \in \{a, b\}} \min\big\{ c_1(u_1, u_2),\ c_0(u_1, u_2) + C(\mathrm{Break}) \big\}, \qquad c_0(v_1, v_2) = \sum_{u \in \{a, b\}} \min\big\{ c_0(u_1, u_2),\ c_1(u_1, u_2) + C(\mathrm{Gain}) \big\},$$

and duplication cases minimize over which duplication comes first or whether both genes duplicate together (an adjacency duplication). Backtracking from the optimal root value constructs an optimal forest; the running time is polynomial in the gene-tree sizes.

## Depends on

- [Sankoff recursion at an internal node](../../small-parsimony-problem/sankoff-node.md)

## Expansion

The presence or absence of an ancestral adjacency is a binary character evolving along the pair of gene trees rather than along the species tree, so the recurrence generalizes Sankoff's weighted small-parsimony algorithm for a binary alphabet: present-to-absent along a branch costs a breakage and absent-to-present a gain. Independence of distinct adjacencies (no explicit inversion or translocation model) is what makes the problem decompose into pairs of gene trees and become polynomial, at the price of not charging duplications and losses in the objective and of allowing ancestral genes in more than two adjacencies (non-linear ancestral genomes). Without duplications and losses the method reduces to Fitch–Sankoff parsimony for adjacency presence on the species tree.

## Sources

- S. Bérard, C. Gallien, B. Boussau, G. J. Szöllősi, V. Daubin and E. Tannier, "Evolution of gene neighborhoods within reconciled phylogenies", Bioinformatics 28 (2012), i382–i388, Sections 2 and 4 (Lemma 1, Theorem 1, recurrence Cases 1–6, backtracking), <https://doi.org/10.1093/bioinformatics/bts374>, PMCID: PMC3436801.
