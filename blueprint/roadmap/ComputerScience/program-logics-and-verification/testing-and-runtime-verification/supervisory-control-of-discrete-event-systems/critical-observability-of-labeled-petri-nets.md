# Critical observability of labeled Petri nets is undecidable

A partially observed system is critically observable when every observation tells whether the current state is critical. For labeled Petri nets with an infinite and co-infinite set of critical markings this is undecidable, while it is decidable when the set of critical markings is finite or co-finite.

**Setting (Masopust).** A *labeled Petri net* $G = (N, M_0, \Sigma, \ell)$ is a [Petri net](../../../concurrent-systems-and-protocols/petri-nets/place-transition-petri-nets.md) $(N, M_0)$ with a labeling $\ell : T \to \Sigma \cup \{\varepsilon\}$ of its transitions; transitions labeled $\varepsilon$ are unobservable. Its language $L(G)$ is the set of labels $\ell(\sigma)$ of firing sequences $\sigma$ from $M_0$, $R(G)$ is its set of reachable markings, and for $w \in L(G)$, $R(G, w)$ is the set of markings reached by firing sequences with label $w$. For a set $C$ of *critical markings*, $G$ is *critically observable* with respect to $C$ if for every $w \in L(G)$,

$$
R(G, w) \subseteq C \quad \text{or} \quad R(G, w) \subseteq R(G) \setminus C .
$$

**Theorem (Masopust).** Critical observability of labeled Petri nets is undecidable.

In the reduction the set $C$ is neither finite nor co-finite; it is built from the reachability set of a second Petri net. The same paper proves that for a finite or co-finite set $C$ the problem is decidable and as hard as Petri net non-reachability, and that critical observability is NL-complete for finite automata and PSPACE-complete for networks of finite automata.

## Depends on

- [Place/transition Petri nets](../../../concurrent-systems-and-protocols/petri-nets/place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Inclusion of reachability sets of Petri nets is undecidable](../../../concurrent-systems-and-protocols/petri-nets/decision-procedures/decision-problems-for-nets-and-vass/equivalence-language-and-behavioural-properties/reachability-set-inclusion-is-undecidable.md)

## Expansion

The proof reduces the inclusion problem $R(A) \subseteq R(B)$ for Petri nets $A$ and $B$ (Hack). The net $G$ starts with a token in a control place and, by one of two unobservable transitions, starts running either $A$ or $B$; a third place carries self-loops labeled by every label of $A$, so that the $B$ branch can mimic every observation of the $A$ branch while staying at the initial marking of $B$. With critical markings consisting of the initial marking and all markings that agree with a marking of $R(B)$ on either copy, $G$ is critically observable exactly when $R(A) \subseteq R(B)$: a marking of $R(A) \setminus R(B)$ is non-critical while the mimicking $B$ branch, with the same observation, is critical.

## Sources

- Tomáš Masopust, *Critical Observability for Automata and Petri Nets*, IEEE Transactions on Automatic Control 65 (2020), no. 1, 341–346, https://doi.org/10.1109/TAC.2019.2912484; the definition of critical observability for labeled Petri nets and the undecidability theorem in the section on Petri nets, read in arXiv:1808.00261v2. Locators in arXiv:1808.00261v2: Theorems 3, 5, 7, 10 and 11.
