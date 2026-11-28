# Local predicate transformers

A predicate transformer maps postconditions monotonically to preconditions. It is local for a set $X$ of modifiable variables when separately conjoining any predicate independent of $X$ commutes into its argument, which says exactly that the frame rule is valid for it; the weakest liberal and weakest preconditions of commands are the operational instances.

States are pairs $(s, h)$ of a store $s$ from variables to integers and a heap $h$, $\mathrm{States}$ is the set of all states, and $\mathrm{Pred}$ is the set of predicates, the subsets of $\mathrm{States}$, with

$$p \ast q = \{(s, h \ast h') : (s, h) \in p,\ (s, h') \in q,\ h \# h'\},$$

$\forall X.\, p = \{(s, h) : (s[s_X], h) \in p \text{ for all } s_X : X \to \mathbb{Z}\}$, and $X \# p$ meaning $p = \forall X.\, p$. Let $\mathrm{PT}$ be the set of [predicate transformers](../../refinement/predicate-transformers-and-refinement.md) on these predicates, the monotone maps $\mathrm{Pred} \to \mathrm{Pred}$ ordered pointwise by inclusion; a transformer $t$ satisfies the triple $\{p\}\, t\, \{q\}$ when $p \subseteq t(q)$, and monotonicity is validity of the rule of consequence. For a set $X$ of variables, $t \in \mathrm{PT}$ is *local for* $X$ if

$$X \# r \implies t(q) \ast r \subseteq t(q \ast r) \qquad \text{for all } q, r \in \mathrm{Pred},$$

equivalently, if $X \# r$ and $p \subseteq t(q)$ imply $p \ast r \subseteq t(q \ast r)$. The local transformers form $\mathrm{LPT}(X)$, a complete sublattice of $\mathrm{PT}$ in the sense of [complete lattices](../../../../Order/lattices-boolean-algebras/complete-lattice.md): joins and meets of families of local transformers are computed pointwise by union and intersection.

For a command $C$ of the heap language,

$$\mathrm{wlp}(C)(q) = \{(s, h) : C, s, h \text{ is safe and every terminal state reached from it satisfies } q\},$$

and $\mathrm{wp}(C)(q)$ is defined in the same way with "must terminate normally" in place of "is safe". The transformer $\lambda q.\, \{(s, h) \in q : |\mathrm{dom}(h)| \le 3\}$ corresponds to a command that faults when more than three cells are allocated and skips otherwise; that command does not satisfy safety monotonicity, and the frame rule is not valid for $\mathrm{PT}$ as a whole.

## Depends on

- [Complete lattice](../../../../Order/lattices-boolean-algebras/complete-lattice.md)
- [Predicate transformers and refinement](../../refinement/predicate-transformers-and-refinement.md)
- [Safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md)

## Proof depends on

- [Complete lattice](../../../../Order/lattices-boolean-algebras/complete-lattice.md)

## Expansion

Closure under joins: $(\bigcup_i t_i(q)) \ast r = \bigcup_i (t_i(q) \ast r) \subseteq \bigcup_i t_i(q \ast r)$, since $\ast$ distributes over unions; closure under meets holds because $\ast$ is monotone, and the empty meet $\lambda q.\, \mathrm{States}$ is local. The three-cell transformer is not local for any $X$: with $q = \mathrm{States}$ and $r$ the set of states whose heap has four cells, $t(q) \ast r$ contains the states with four cells (from the empty heap) while $t(q \ast r)$ contains none. The source further states that $\mathrm{wp}(C)$ and $\mathrm{wlp}(C)$ are both local for $X$ if and only if $C$ satisfies [safety monotonicity, termination monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md) and every terminal store reached from a safe configuration agrees with the initial store on the variables outside $X$, and that no property of unsafe configurations can be recovered, both transformers ignoring them; the conference version states Proposition 2 without proof and refers to Yang's thesis for the tie-up between transformers and relations. Local predicate transformers are the semantic domain of [adaptation completeness of the frame rule](adaptation-completeness-of-the-frame-rule.md).

## Sources

- H. Yang and P. O'Hearn, "A semantic basis for local reasoning", *Foundations of Software Science and Computation Structures (FoSSaCS 2002)*, LNCS 2303, Springer, 2002, pp. 402–416, <https://doi.org/10.1007/3-540-45931-6_28>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf>, Section 3 (states, $\ast$, $\forall X.\, p$ and $X \# p$), Section 5.1 ($\mathrm{PT}$, the locality condition for $X$, $\mathrm{LPT}(X)$, the three-cell example with its footnote, Proposition 1 and its proof) and Section 5.2 ($\mathrm{wp}$, $\mathrm{wlp}$ and Proposition 2).
