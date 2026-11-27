# de Rezende et al.: automating Nullstellensatz and Polynomial Calculus is NP-hard

Given an unsatisfiable CNF formula $F$, it is NP-hard to find a refutation of $F$ in the Nullstellensatz or Polynomial Calculus proof systems (over any fixed field) in time polynomial in the size of the shortest such refutation. The proof also gives a simplified proof of the Atserias-Müller theorem via size-width trade-offs.

## Proof sketch

Replace the relativized pigeonhole component of the Atserias-Müller construction by a lifted formula whose algebraic degree lower bound transfers to size via a degree-to-size relation for the respective system, and observe that the satisfiable case still admits short algebraic refutations simulating resolution line by line.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Proof depends on

- [Atserias–Müller: automating resolution is NP-hard](atserias-muller.md)

## Sources

- S. F. de Rezende, M. Göös, J. Nordström, T. Pitassi, R. Robere, D. Sokolov, "Automating algebraic proof systems is NP-hard", STOC (2021), ECCC TR20-064.
