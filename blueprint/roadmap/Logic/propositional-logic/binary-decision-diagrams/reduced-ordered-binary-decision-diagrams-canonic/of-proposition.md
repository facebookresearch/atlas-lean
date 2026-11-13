# Diagram of a proposition

Each proposition $A$ whose atoms are natural numbers is sent
to a binary decision diagram by recursion on $A$: an atom $x$ goes to the node testing $x$ with
the leaf false as its false-child and the leaf true as its true-child, and a conjunction
$A \wedge B$, disjunction $A \vee B$ or implication $A \to B$ goes to the result of apply on the
diagrams of $A$ and $B$ under the Boolean operation and, or, or $(a, b) \mapsto \lnot a \lor b$
respectively.
