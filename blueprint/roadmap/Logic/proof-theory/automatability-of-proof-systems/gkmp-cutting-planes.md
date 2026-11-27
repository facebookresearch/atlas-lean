# Göös–Koroth–Mertz–Pitassi: automating cutting planes is NP-hard

Given an unsatisfiable CNF formula $F$, it is NP-hard to find a cutting planes refutation of $F$ in time polynomial in the length of the shortest cutting planes refutation. Moreover, unless the Gap-Hitting-Set problem has a non-trivial algorithm, tree-like cutting planes refutations cannot be found in time polynomial in the shortest tree-like refutation.

## Proof sketch

Follow the Atserias-Müller template, proving the required lower bound in the unsatisfiable case by two new lifting theorems: dag-like lifting for gadgets with many output bits, which converts resolution width lower bounds into cutting planes size lower bounds, and a tree-like lifting theorem simulating $r$-round protocols with gadgets of query complexity $O(\log r)$ independent of input length.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Proof depends on

- [Atserias–Müller: automating resolution is NP-hard](atserias-muller.md)
- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)

## Sources

- M. Göös, S. Koroth, I. Mertz, T. Pitassi, "Automating cutting planes is NP-hard", STOC (2020), arXiv:2004.08037.
