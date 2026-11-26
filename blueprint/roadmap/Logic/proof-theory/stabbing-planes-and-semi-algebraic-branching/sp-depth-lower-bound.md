# Communication-based depth lower bounds for stabbing planes

Every stabbing planes refutation of depth $d$ of a CNF formula $F$ with a variable partition $X \cup Y$ yields a randomized communication protocol of cost $O(d \log n)$ for the falsified-clause search problem of $F$ under that partition (each linear query is evaluated by a public-coin protocol for comparing $a_X \cdot x$ with $b - a_Y \cdot y$). Consequently, lifted formulas whose search problems have randomized communication complexity $n^{\Omega(1)}$ require stabbing planes depth $n^{\Omega(1)}/\log n$.

## Proof sketch

Walk down the refutation tree from the root, at each node using the randomized greater-than protocol of cost $O(\log n)$ with error $1/\operatorname{poly}(n)$ to decide which branch contains the joint input; the leaf reached is an empty polytope whose certificate identifies a falsified clause. Lower bounds for lifted search problems then follow from randomized lifting theorems.

## Depends on

- [The stabbing planes proof system](stabbing-planes-system.md)
- [Public-coin randomized protocol](../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/public-coin-protocol.md)

## Proof depends on

- [Göös–Pitassi–Watson: query-to-communication lifting for BPP](../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/gpw-bpp-lifting.md)

## Sources

- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", CCC (2021), arXiv:2102.05019.
- P. Beame, N. Fleming, R. Impagliazzo, A. Kolokolova, D. Pankratov, T. Pitassi, R. Robere, "Stabbing planes", ITCS (2018), arXiv:1710.03219.
