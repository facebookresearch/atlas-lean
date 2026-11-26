# Typed terms give natural-deduction derivations

Assume equality of base types is decidable. Read each simple type over base types as an implicational proposition over the same atoms, base types as atoms and arrows as implications, and a context of types as the set of propositions its types denote. Then for every intrinsically typed term $t$ of type $A$ in context $\Gamma$ of the simply typed lambda calculus, the proposition denoted by $A$ is derivable in natural deduction for implicational logic from the hypotheses denoted by $\Gamma$, in every theory: a variable becomes the assumption of its type, an application becomes implication elimination, and an abstraction becomes implication introduction.

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapter 3, "The Curry-Howard isomorphism", <https://www.paultaylor.eu/stable/prot.pdf>
