# Anari-Liu-Oveis Gharan-Vinzant: rapid mixing of the matroid basis exchange walk

For every matroid of rank $r$ on $n$ elements, the bases-exchange walk (down-up walk on bases) has spectral gap at least $1/r$, hence mixes in time polynomial in $r$ and $\log n$ (for instance $O(r^2\log n)$ from the spectral gap and the bound $1/\binom{n}{r}$ on the smallest stationary probability); consequently there is a fully polynomial randomized approximation scheme for the number of bases of any matroid given by an independence oracle, proving the Mihail-Vazirani conjecture on edge expansion of the bases polytope.

## Proof sketch

The basis generating polynomial is Lorentzian (completely log-concave), and log-concavity of all its partial derivatives at the all-ones point says exactly that the $1$-skeleton of every link of the matroid's independence complex has second eigenvalue at most $0$, i.e. the complex is a $0$-local spectral expander. The Kaufman-Oppenheim local-to-global theorem with $\gamma = 0$ gives gap $1/r$ for the top down-up walk; standard Jerrum-Valiant-Vazirani reductions give the counting algorithm.

## Depends on

- [Up-down and down-up random walks on simplicial complexes](up-down-random-walks-on-simplicial-complexes.md)

## Proof depends on

- [Kaufman-Oppenheim: local spectral expansion controls high-order random walks](kaufman-oppenheim-high-order-walks.md)
- [Basis generating polynomials of matroids are Lorentzian](../../../Combinatorics/matroid-theory/lorentzian-polynomials/basis-generating-polynomial-mem-l.md)
- [The set of Lorentzian polynomials](../../../Combinatorics/matroid-theory/lorentzian-polynomials/l.md)

## Sources

- Nima Anari, Kuikui Liu, Shayan Oveis Gharan, Cynthia Vinzant, "Log-concave polynomials II: high-dimensional walks and an FPRAS for counting bases of a matroid", Annals of Mathematics 199(1) (2024), STOC (2019); arXiv:1811.01816.
