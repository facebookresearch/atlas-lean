# Cut elimination for the intuitionistic sequent calculus LJ

This node covers Gentzen's sequent calculus LJ for intuitionistic first-order logic and its cut
elimination theorem (Hauptsatz).

LJ is the special case of the classical sequent calculus LK in which every succedent contains at
most one formula. The main result: for a first-order language whose symbols have decidable
equality, every sequent $\Gamma \Rightarrow \Delta$, with $\Delta$ empty or a single formula, that
is derivable in LJ has a derivation of the same sequent in LJ that uses no instance of the cut rule.
Every connective and both quantifiers are in scope, with the eigenvariable (freshness) conditions of
the quantifier rules; no bound on the size of the cut-free derivation is part of the statement.

## Expansion

A sound expansion fixes one presentation of LJ (contexts as lists or as multisets, with the
structural rules that presentation needs, and its freshness conditions) and has separate pages for:
the calculus; cut-free derivations as a predicate on derivations; admissibility of cut; cut
elimination, including sequents with empty succedent; and the subformula property of cut-free
derivations as a corollary. Cut elimination for classical LK does not by itself give this result,
since LK derivations of single-succedent sequents may use multiple succedents.

## Sources

- J. von Plato, *The development of proof theory*, Stanford Encyclopedia of Philosophy,
  substantive revision 13 October 2014, section on natural deduction and sequent calculus.
  <https://plato.stanford.edu/entries/proof-theory-development/>
