# Symbolic CTL model checking with BDDs

Let a finite Kripke structure have a total transition relation (every state has a successor). Encode its states injectively as bit vectors of length $n \ge \lceil \log_2 |S| \rceil$, and represent sets of states, its transition relation $R(\bar v, \bar v')$ and each atomic proposition by reduced ordered binary decision diagrams; bit vectors that encode no state are excluded, so negation is taken relative to the set of encoded states. For a set of states given by a BDD $S(\bar v)$, the BDD $\mathrm{EX}\,S = \exists \bar v'.\, (R(\bar v, \bar v') \wedge S(\bar v'))$ (the relational product, with $S$ renamed to the primed variables) denotes the set of states with a successor in $S$. Computing $\mathbf{EX}$ in this way, $\mathbf{E}[\varphi\, \mathbf{U}\, \psi]$ as the least fixed point of $Z \mapsto \psi \vee (\varphi \wedge \mathrm{EX}\, Z)$ and $\mathbf{EG}\,\varphi$ as the greatest fixed point of $Z \mapsto \varphi \wedge \mathrm{EX}\, Z$, by iteration until the BDDs stabilize, yields for every CTL formula a BDD denoting exactly the set of states that satisfy it.

## Proof depends on

- [Reduced ordered diagrams are equal iff they have the same values](../../propositional-logic/binary-decision-diagrams/reduced-ordered-binary-decision-diagrams-canonic/eq-iff-eval-eq.md)
- [Finite-state CTL model checking by structural recursion](../model-checking-for-computation-tree-logic/sat.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- BDD quantification, renaming, and relational product with their correctness (proof prerequisite)

## Sources

- J. R. Burch, E. M. Clarke, K. L. McMillan, D. L. Dill and L. J. Hwang, "Symbolic model checking: 10^20 states and beyond", *Information and Computation* 98(2):142–170, 1992
- E. M. Clarke, O. Grumberg and D. A. Peled, *Model Checking*, MIT Press, 1999
- J.-P. Katoen, *Model Checking*, Lectures 18 and 19: Reduced ordered binary decision diagrams; Symbolic model checking with BDDs, RWTH Aachen University, 2019, <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019_handout_lec18.pdf>, <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019_handout_lec19.pdf>
