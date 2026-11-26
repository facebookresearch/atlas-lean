# Bundles in a strand space

Let $\Sigma$ be a [strand space](strand-spaces.md) with nodes $\mathcal N$ and edges $\to$ and $\Rightarrow$. A subgraph $\mathcal C = \langle \mathcal N_{\mathcal C}, (\to_{\mathcal C} \cup \Rightarrow_{\mathcal C})\rangle$
with $\to_{\mathcal C} \subseteq \to$ and $\Rightarrow_{\mathcal C} \subseteq \Rightarrow$ is a *bundle* if

1. $\mathcal C$ is finite;
2. every node $n_2 \in \mathcal N_{\mathcal C}$ with a negative term has a unique $n_1$ with $n_1 \to_{\mathcal C} n_2$;
3. if $n_2 \in \mathcal N_{\mathcal C}$ and $n_1 \Rightarrow n_2$, then $n_1 \Rightarrow_{\mathcal C} n_2$;
4. $\mathcal C$ is acyclic.

So each received message was sent by a unique node of the bundle, and every node of the bundle has its strand predecessors in the bundle. For a set $S$ of edges,
$\prec_S$ is its transitive closure and $\preceq_S$ its reflexive transitive closure; for a bundle, $\preceq_{\mathcal C}$ expresses causal precedence.

## Depends on

- [Strand spaces](strand-spaces.md)

## Sources

- F. J. Thayer Fábrega, J. C. Herzog and J. D. Guttman, "Strand spaces: proving security protocols correct", *Journal of Computer Security* 7:191–230, 1999, copy at <http://web.cs.wpi.edu/~guttman/pubs/jcs_strand_spaces.pdf>: Section 2.2 (Definition 2.4, Notational Convention 2.5 and Definition 2.6).
