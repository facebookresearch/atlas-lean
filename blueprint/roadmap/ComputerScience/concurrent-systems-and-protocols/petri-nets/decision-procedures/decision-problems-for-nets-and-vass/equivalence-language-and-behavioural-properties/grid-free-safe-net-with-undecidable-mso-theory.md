# A grid-free 1-safe Petri net with undecidable MSO theory

There is a finite 1-safe Petri net system whose event structure unfolding contains no grid but has an undecidable monadic second-order theory. This refutes Thiagarajan's conjecture that, for such systems, decidability of the MSO theory is equivalent to grid-freeness.

**Setting (Chalopin and Chepoi).** An *event structure* $\mathcal{E} = (E, \le, \#)$ has a set $E$ of events, a partial order $\le$ of causal dependency in which every event has finitely many predecessors, and an irreflexive symmetric conflict relation $\#$ such that $e \# e'$ and $e' \le e''$ imply $e \# e''$. A finite 1-safe Petri net system $N$ with labeled transitions unfolds into a labeled event structure $\mathcal{E}_N$; event structures arising in this way are called *trace-regular*. The *MSO theory* of $N$ is the set of monadic second-order sentences, over the relational structure $(E, (R_a)_a, \le)$ with a unary predicate $R_a$ for the events labeled $a$, that hold in $\mathcal{E}_N$. An event structure is *grid-free* (Thiagarajan and Yang) if there are no pairwise disjoint sets $X = \{x_0 < x_1 < \cdots\}$, $Y = \{y_0 < y_1 < \cdots\}$ and $Z$ of events with every $x_i$ concurrent with every $y_j$ (neither ordered nor in conflict) and an injective map $g : X \times Y \to Z$ such that $g(x_i, y_j)$ lies above $x_i$ and $y_j$ but above no $x_{i'}$ with $i' > i$ and no $y_{j'}$ with $j' > j$.

**Theorem (Chalopin and Chepoi).** There is a finite 1-safe net system whose event structure unfolding is grid-free and has an undecidable MSO theory. Concretely, there are a virtually special nonpositively curved square complex $Z$ and a trace-regular event structure $\mathcal{E}_Z$ whose domain is a principal filter of the universal cover of $Z$, such that the event structure $\dot{\mathcal{E}}_Z$ obtained from $\mathcal{E}_Z$ by adding, for each configuration $c$ (finite, conflict-free, downward-closed set of events), a new event $e_c$ above exactly the events of $c$ and in conflict with all other events is trace-regular and grid-free and $\mathrm{MSO}(\dot{\mathcal{E}}_Z)$ is undecidable.

Thiagarajan and Yang had shown that the MSO theory of a net system that is not grid-free is undecidable.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The domain of an event structure, its set of configurations ordered by inclusion, has a median graph. The authors build a square complex $Z$ from three squares with one vertex and four colored edges, show that it is virtually special, and use their correspondence between virtually special square complexes and trace-regular event structures to obtain $\mathcal{E}_Z$. The median graph of the domain of $\dot{\mathcal{E}}_Z$ has bounded hyperbolicity, which forces grid-freeness, and unbounded treewidth. MSO sentences over the event structure can express MSO properties of this graph, and graphs of unbounded treewidth from such a family have an undecidable MSO theory by results of Seese, Courcelle, and Muller and Schupp. A good expansion links pages for Seese's theorem and for the correspondence between virtually special square complexes and trace-regular event structures.

## Sources

- Jérémie Chalopin and Victor Chepoi, *1-Safe Petri Nets and Special Cube Complexes: Equivalence and Applications*, ACM Transactions on Computational Logic 20 (2019), no. 3, pp. 1–49, https://doi.org/10.1145/3322095; the definitions of event structures, MSO theories and grid-freeness in Section 2 and the counterexample theorem with its proof, read in arXiv:1810.03395v2. Locators in arXiv:1810.03395v2: Theorem 10.1, Lemma 10.6 and Theorem 9.11.
