# Efficient adversaries

In the asymptotic setting, an *efficient adversary* is a probabilistic algorithm that runs in time polynomial in the security parameter $\lambda$, given as a single uniform machine whose input includes $1^\lambda$; equivalently, a family $(A_\lambda)_\lambda$ computed by one uniform probabilistic polynomial-time machine. A function $\varepsilon(\lambda)$ is *negligible* if $\varepsilon(\lambda) = O(\lambda^{-c})$ for every $c$, and a scheme is secure if every efficient adversary has negligible advantage in the security game. In the concrete setting one instead bounds the advantage of every adversary with given running time and number of oracle queries.

## Depends on

- [Polynomial-time many-one reduction](../../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)
- [Adaptive oracle algorithms](../oracle-algorithms/oracle-comp.md)
- [Probabilistic polynomial-time Turing machines](probabilistic-polynomial-time-turing-machines.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>
- R. Pass and A. shelat, *A Course in Cryptography*, lecture notes, Cornell University, 2010, <https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf>
