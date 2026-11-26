# Haken–Cook / Pudlák: exponential lower bounds for monotone real circuits

There are explicit monotone Boolean functions on $N$ input bits, including the broken mosquito screen function and the clique-versus-coloring separation, such that every monotone real circuit computing them has size $2^{N^{\Omega(1)}}$. In particular every monotone real circuit separating graphs on $n$ vertices containing a $k$-clique from $(k-1)$-colourable graphs, for $k = n^{2/3}$, has size $2^{\Omega((n/\log n)^{1/3})}$.

## Proof sketch

Extend Razborov's method of approximations to monotone real gates: the key observation is that an arbitrary monotone real gate applied to two functions with approximators can be approximated by a monotone threshold of the approximators, and the sunflower-based plucking argument only uses monotonicity of each gate. The counting of approximation errors on random positive and negative test inputs is unchanged up to constants.

## Depends on

- [Monotone real circuits](monotone-real-circuit.md)

## Proof depends on

- [Alon–Boppana: monotone circuits for clique need exponential size](../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md)

## Sources

- A. Haken, S. A. Cook, "An exponential lower bound for the size of monotone real circuits", Journal of Computer and System Sciences 58 (1999) 326-335.
- P. Pudlák, "Lower bounds for resolution and cutting plane proofs and monotone computations", Journal of Symbolic Logic 62 (1997) 981-998.
