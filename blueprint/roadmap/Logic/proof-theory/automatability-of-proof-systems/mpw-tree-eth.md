# Mertz–Pitassi–Wei: short tree-like resolution proofs are hard to find under ETH

Assuming the Exponential Time Hypothesis, tree-like resolution is not automatable in time $n^{o(\log n)}$, where $n$ is the size of the formula plus the size of its shortest tree-like refutation. Together with the $n^{O(\log s)}$-time algorithm, this pins the complexity of automating tree-like resolution to quasi-polynomial time.

## Proof sketch

Reduce a $k$-clique-type problem with gap via a lifted formula whose tree-like refutation size is $n^{\Theta(\text{gap parameter})}$; an $n^{o(\log n)}$ automating algorithm would solve a problem that under ETH requires time $2^{\Omega(k \log n)}$ for suitable $k = \Theta(\log n)$.

## Depends on

- [Tree-like resolution is quasi-polynomially automatable](tree-resolution-quasi-automatable.md)
- [Automatable proof systems](automatable-proof-system.md)

## Sources

- I. Mertz, T. Pitassi, Y. Wei, "Short proofs are hard to find", ICALP (2019).
