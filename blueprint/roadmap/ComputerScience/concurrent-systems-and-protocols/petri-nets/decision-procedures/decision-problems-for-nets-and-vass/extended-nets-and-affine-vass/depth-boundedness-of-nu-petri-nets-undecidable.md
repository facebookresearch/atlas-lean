# Depth-boundedness of Petri nets with name creation is undecidable

In ν-Petri nets, whose tokens are names that transitions can match and freshly create, a net is depth-bounded when no name ever occurs more than a bounded number of times in any place. Deciding depth-boundedness is undecidable, while the dual property of width-boundedness and plain boundedness are decidable.

**Setting (Rosa-Velardo and de Frutos-Escrig).** Fix an infinite set $\mathit{Id}$ of names. A *ν-Petri net* (ν-PN) has finite sets of places and transitions; its arcs are labeled by finite multisets of variables, some of which are *name-creation* variables. A marking $M$ assigns to each place $p$ a finite multiset $M(p)$ of names. A transition fires under a mode that maps its variables to names, injectively and with name-creation variables mapped to names that occur nowhere in the current marking: it removes the instantiated input multisets and adds the instantiated output multisets. A ν-PN with initial marking $M_0$ is *depth-bounded* if there is $n \in \mathbb{N}$ such that for every marking $M$ reachable from $M_0$, every place $p$ and every name $a$, the multiplicity $M(p)(a)$ is at most $n$; it is *width-bounded* if some $n$ bounds the number of distinct names in every reachable marking.

**Theorem (Rosa-Velardo and de Frutos-Escrig).** Depth-boundedness is undecidable for ν-Petri nets.

ν-Petri nets are strictly well-structured, so coverability, termination and boundedness are decidable, and width-boundedness is decidable too; reachability is undecidable, and a net is bounded exactly when it is both width-bounded and depth-bounded. The source notes that an earlier published decidability proof for depth-boundedness was wrong.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces boundedness of reset nets, which Dufourd, Finkel and Schnoebelen proved undecidable. From a reset net $N$ one builds in polynomial time a ν-PN $N^*$ with a copy $\bar{p}$ of each place $p$: $\bar{p}$ holds a single name $a_p$, and the tokens of $p$ in $N$ are the occurrences of $a_p$ in $p$. Resetting $p$ is simulated by replacing $a_p$ with a freshly created name, which strands the old occurrences, so reachable markings of $N$ correspond to reachable markings of $N^*$ through the multiplicities $M^*(p)(a_p)$. Hence $N$ is bounded exactly when $N^*$ is depth-bounded. A good expansion links a page for the undecidability of boundedness of reset nets.

## Sources

- Fernando Rosa-Velardo and David de Frutos-Escrig, *Decidability and complexity of Petri nets with unordered data*, Theoretical Computer Science 412 (2011), no. 34, 4439–4451, https://doi.org/10.1016/j.tcs.2011.05.007, whose abstract, read on the open repository record at https://eprints.ucm.es/id/eprint/20624/, states the undecidability of depth-boundedness; the definitions of ν-PN and of width- and depth-boundedness, the reduction from reset nets and the undecidability proposition are read in the earlier version arXiv:1011.3964v1. Locators in arXiv:1011.3964v1: Propositions 1 and 12.
