# Determinant expansion on the directed species-reaction graph

**Setting.** A reaction system $\dot{\vec x}=\vec N\vec v(\vec x)$ has $n$ species, $r$ reactions, stoichiometric matrix $\vec N$ and rate laws $\vec v$. Kinetics is *non-autocatalytic* (NAC) if $\partial v_j/\partial x_i>0$ when species $S_i$ is a substrate of reaction $R_j$ and all concentrations are positive, and $\partial v_j/\partial x_i\equiv0$ otherwise (mass action and Michaelis-Menten are NAC). The Jacobian is $\vec J=\vec N\,\partial\vec v/\partial\vec x$.

**DSR graph.** The *directed species-reaction graph* $G$ is bipartite on species vertices $V_S$ and reaction vertices $V_R$ with *rate edges* $S_i\to R_j$ labelled $\partial v_j/\partial x_i$ (when not identically zero) and *stoichiometric edges* $R_j\to S_i$ labelled $N_{ij}$ (when nonzero). Each edge $S\to S'$ of the species interaction graph corresponds to the set of 2-paths $S\to R\to S'$. A *species-line-graph* $L$ is a union of vertex-disjoint cycles of $G$ covering every species vertex once; its weight $\lambda(L)$ factors as $\lambda_{SR}(L)\lambda_{RS}(L)$ (rate part and stoichiometric part), and $\sigma(L)=(-1)^{\#\text{even cycles}}$. Two species-line-graphs are *compatible* if they use the same rate edges; for a compatibility class $[L]$ the *stoichiometric term* is the constant $\Lambda([L])=\sum_{L'\in[L]}\sigma(L')\lambda_{RS}(L')$.

**Statements.**

1. For NAC kinetics every sub-graph $H$ of $G$ with at least one stoichiometric edge is sign-definite: $\mathrm{sign}\,\lambda(H)=\mathrm{sign}\,\lambda_{RS}(H)$, independently of $\vec x>0$.
2. *(Expansion by compatibility classes.)*

    $$\det(\vec J)=\sum_{[L]\in\mathcal{L}(G)/\sim}\Lambda([L])\,\lambda_{SR}(L),$$

    where each $\lambda_{SR}(L)>0$ is a product of rate derivatives. Hence $\det\vec J\ge0$ for all $\vec x>0$ if $\Lambda([L])\ge0$ for every class, and $>0$ if in addition one $\Lambda([L])>0$; analogously for non-positivity. The same applies to each principal minor and hence to every coefficient of the characteristic polynomial.

3. *(Graphical sufficient condition.)* In $G(-\vec J)$, $\det(-\vec J)>0$ for all $\vec x>0$ provided (a) at least one stoichiometric term is positive, (b) every cycle is either a positive cycle or is dominated by the line-graph its species induce, and (c) no two negative cycles intersect along a path starting in $V_S$ and ending in $V_R$. With all principal minors of $-\vec J$ positive, the system is injective and cannot be multistationary.

## Expansion

Expanding $\det(\vec N\,\vec D)$ with $\vec D=\partial\vec v/\partial\vec x$ by the Cauchy-Binet formula pairs each permutation (a cycle cover of the interaction graph) with choices of a reaction through which each interaction passes, which are exactly the species-line-graphs of $G$. Terms sharing the same rate edges carry the same monomial in the rate derivatives, so grouping them leaves the constant $\Lambda([L])$, which equals $\pm\det(\vec N_L)$ for the corresponding square submatrix of the stoichiometry. Negative stoichiometric terms can only arise when two negative cycles share a species-to-reaction intersection, so excluding such intersections and dominated cycles forces every class to contribute with the same sign.

## Sources

- Hans-Michael Kaltenbach, "A Unified View on Bipartite Species-reaction Graphs and Their Relation to Interaction Graphs and Qualitative Dynamics of Chemical Reaction Networks", Electronic Notes in Theoretical Computer Science 350 (2020), 73–90, <https://doi.org/10.1016/j.entcs.2020.06.005>; numbering as in arXiv:1210.0320: Definition 5.1, Proposition 5.2, Definition 6.5, Theorem 6.7, Proposition 6.12, Theorem 6.13 and Corollary 6.14.
