# Alekhnovich–Razborov: resolution is not automatable unless W[P] is tractable

If tree-like or general resolution is automatable (even within quasi-polynomial factors in a parameterized sense), then the parameterized class $\mathrm{W}[\mathrm{P}]$ is contained in randomized fixed-parameter tractable time, i.e. $\mathrm{W}[\mathrm{P}] \subseteq \mathrm{co\text{-}FPR}$. In particular, unless $\mathrm{W}[\mathrm{P}]$ is tractable, resolution is not automatable.

## Proof sketch

Reduce the parameterized minimum monotone circuit satisfying assignment problem to automatability: from a monotone circuit build a CNF whose shortest resolution refutation size is $n^{\Theta(k)}$ where $k$ is the minimum weight of a satisfying assignment of the circuit, using a lifting of a combinatorial pebbling-type principle. An automating algorithm then approximates $k$ to within a constant factor, which is $\mathrm{W}[\mathrm{P}]$-hard by gap amplification.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Sources

- M. Alekhnovich, A. A. Razborov, "Resolution is not automatizable unless W[P] is tractable", SIAM Journal on Computing 38 (2008) 1347-1363; FOCS (2001).
