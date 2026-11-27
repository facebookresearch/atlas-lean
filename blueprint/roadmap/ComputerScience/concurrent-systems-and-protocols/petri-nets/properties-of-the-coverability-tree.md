# Properties of the coverability tree

For every [Petri net](place-transition-petri-nets.md) $(N, M_0)$ the construction of the [coverability tree](coverability-tree.md) terminates, and the finite tree $T$ it produces satisfies:

1. $(N, M_0)$ is [bounded](boundedness-and-safeness.md), so that $R(M_0)$ is finite, if and only if $\omega$ appears in no node label of $T$;
2. $(N, M_0)$ is safe if and only if only $0$'s and $1$'s appear in node labels of $T$;
3. a transition is dead if and only if it labels no arc of $T$;
4. if $M$ is reachable from $M_0$, then some node of $T$ is labelled $M'$ with $M \le M'$.

Because $\omega$ forgets how a place grows, the coverability tree does not decide reachability or liveness: two nets, one live and one not, can have the same coverability tree.

## Depends on

- [The coverability tree](coverability-tree.md)
- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Proof depends on

- [Kőnig's lemma for inverse systems](../../process-calculi/csp-semantic-models/konig-s-lemma-for-inverse-systems.md)

## Expansion

This page becomes ready once the proof of termination is linked. It needs:

- Dickson's lemma: every infinite sequence of vectors in $\mathbb{N}^k$ has two terms $A_m \le A_n$ with $m < n$ (proof prerequisite of termination)
- the step combining Kőnig's lemma, applied to the levels of the tree with the ancestor maps, and Dickson's lemma: along an infinite path no label repeats an earlier one, so Dickson's lemma, applied to the places that are not yet $\omega$, gives a strictly larger later label and with it a new $\omega$, which can happen at most once per place (proof of termination)
- the soundness and completeness arguments for properties 1–4, relating firing sequences of the net to paths of the tree (proof of the properties)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section V-A: properties 1)–4) of the coverability tree, and Figs. 18–20 (two nets with the same coverability tree, one live and one not).
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraph "Boundedness" (the coverability tree of Karp and Miller and its non-primitive-recursive size).
