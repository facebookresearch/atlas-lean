# Non-reachability in Petri nets has a semilinear inductive invariant

Let $(N, M_0)$ be an ordinary Petri net whose net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition, and $M_1$ a marking of $N$. If $M_1$ is not reachable from $M_0$, then there is a [semilinear set](../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md) $\mathcal{M}$ of markings of $N$ such that

1. $M_0 \in \mathcal{M}$;
2. if $M \in \mathcal{M}$ and $M [t\rangle M'$ for a transition $t$, then $M' \in \mathcal{M}$; and
3. $M_1 \notin \mathcal{M}$.

Conversely, a set with these three properties shows that $M_1$ is not reachable from $M_0$.

## Depends on

- [Semilinear set of vectors](../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Expansion

This page needs a decomposition before its proof prerequisites can be listed. A good expansion follows Leroux's proof: the Kosaraju–Lambert–Mayr–Sacerdote–Tenney decomposition into perfect marked graph-transition sequences (Theorem 3.7 of the cited paper), the semi-pseudo-linearity of the Parikh images of their languages (Theorem 5.3 and Corollary 5.4), the Petri-set property of reachability sets from semilinear sets (Theorem 6.4), the dimension theory of pseudo-linear sets (Section 7), and the extension of Presburger separators to complete ones (Lemma 8.2 and Theorem 8.3), each on its own page.

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 3.2.24 ("Leroux 2012"), stated without proof, p. 66.
- J. Leroux, "The general vector addition system reachability problem by Presburger inductive invariants", *Logical Methods in Computer Science* 6(3:22), 2010, <https://arxiv.org/abs/1009.1076>, Corollary 8.4 (for vector addition systems, with an inductive invariant given by a Presburger formula) and the Conclusion.
