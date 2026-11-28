# Branching-time ALC with rigid roles is undecidable over general TBoxes

Concept satisfiability with respect to general TBoxes is undecidable for the combination of the description logic ALC with the branching-time temporal logic CTL in the presence of rigid roles, already with only the operators "possibly eventually" and "inevitably always".

**Theorem (Gutiérrez-Basulto, Jung and Schneider).** Let the role names be partitioned into rigid and local role names. Concepts of $\mathrm{CTL}_{\mathcal{ALC}}$ are

$$
C ::= \top \mid A \mid \neg C \mid C \sqcap D \mid \exists r.C \mid \mathsf E\bigcirc C \mid \mathsf E\Box C \mid \mathsf E(C\,\mathcal U\,D),
$$

with $\mathsf E\Diamond C = \mathsf E(\top\,\mathcal U\,C)$ and $\mathsf A\Box C = \neg\mathsf E\Diamond\neg C$. A *temporal interpretation* $\mathcal I = (\Delta, T, \{\mathcal I_w\}_{w \in W})$ consists of an infinite tree $T = (W, E)$ in which every node has a successor, and of an ALC interpretation $\mathcal I_w$ with the same domain $\Delta$ for each node $w$, such that every rigid role name has the same interpretation at all nodes. Concepts are interpreted at nodes: $\mathsf E\bigcirc C$, $\mathsf E\Box C$ and $\mathsf E(C\,\mathcal U\,D)$ hold of $d$ at $w$ if, along some path starting at $w$, $d$ satisfies $C$ at the next node, at every node, or until $D$, respectively. A general TBox is a finite set of concept inclusions $C \sqsubseteq D$, satisfied when $C^{\mathcal I, w} \subseteq D^{\mathcal I, w}$ at every node $w$; a concept $C$ is satisfiable with respect to a TBox $\mathcal T$ if some model of $\mathcal T$ has $C^{\mathcal I, \varepsilon} \neq \emptyset$ at the root $\varepsilon$. Then concept satisfiability with respect to general TBoxes is undecidable, with rigid roles, for the fragment $\mathrm{CTL}^{\mathsf E\Diamond, \mathsf A\Box}_{\mathcal{ALC}}$ whose only temporal operators are $\mathsf E\Diamond$ and $\mathsf A\Box$, and for its variant with the strict versions of these operators (Theorem 2 of the source).

The same paper shows that concept subsumption with respect to general TBoxes is undecidable for several fragments of the lightweight logic $\mathrm{CTL}_{\mathcal{EL}}$, among them the one with $\mathsf E\Diamond$ and $\mathsf E\Box$ (its Theorem 4), because these fragments can simulate disjunction. Over empty or acyclic TBoxes, $\mathrm{CTL}_{\mathcal{ALC}}$ with rigid roles is decidable but inherently nonelementary (Gutiérrez-Basulto, Jung and Schneider, IJCAI 2015).

## Depends on

- [ALC syntax, semantics and reasoning tasks](../../alc-syntax-semantics-and-reasoning-tasks.md)
- [CTL formulas](../../../temporal-logic/computation-tree-logic/formula.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof starts from the result of Gabelaia et al. that satisfiability is undecidable for a family of transitive products of modal logics including $\mathrm{S4} \times \mathrm{K4}$: rephrased in this notation, it is undecidable whether a $\mathrm{CTL}^{\mathsf E\Diamond, \mathsf A\Box}_{\mathcal{ALC}}$ concept with one rigid role $r$ and no other roles is satisfiable in a temporal interpretation in which $r$ is transitive at every node (Theorem 1 of the source). Using a technique of Tobies, transitivity of $r$ is then simulated by a general TBox, which reduces this problem to concept satisfiability with respect to general TBoxes. A good expansion links the undecidability of the product logics of Gabelaia et al.

## Sources

- V. Gutiérrez-Basulto, J. C. Jung and T. Schneider, "Lightweight description logics and branching time: a troublesome marriage", in *Proceedings of the Fourteenth International Conference on Principles of Knowledge Representation and Reasoning (KR 2014)*, AAAI Press, 2014; read in the [open-access author copy](http://www.informatik.uni-bremen.de/tdki/research/papers/2014/GJS-KR14.pdf): Section 2 (the logic $\mathrm{CTL}_{\mathcal{ALC}}$, temporal interpretations, TBoxes), Section 3 (Theorems 1 and 2) and Section 4.1 (Theorem 4).
- V. Gutiérrez-Basulto, J. C. Jung and T. Schneider, "Lightweight temporal description logics with rigid roles and restricted TBoxes", in *Proceedings of the Twenty-Fourth International Joint Conference on Artificial Intelligence (IJCAI 2015)*, AAAI Press, 2015, pp. 3015–3021; read in the [open-access copy](https://ijcai.org/proceedings/2015/0426.pdf): the abstract, Section 1 and Table 1 (decidability over empty and acyclic TBoxes).
