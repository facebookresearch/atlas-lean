# Covering product and the zeta transform

For $f, g$ on the subsets of an $n$-element set with values in a commutative ring, the *covering product* $(f *_c g)(X) = \sum_{A \cup B = X} f(A) g(B)$ satisfies $\zeta(f *_c g) = \zeta f \cdot \zeta g$ pointwise. Hence $f *_c g = \mu(\zeta f \cdot \zeta g)$ can be computed with $O(2^n n)$ ring operations (Björklund–Husfeldt–Kaski–Koivisto).

## Proof sketch

$\zeta(f *_c g)(S) = \sum_{A \cup B \subseteq S} f(A)g(B) = \sum_{A \subseteq S} f(A) \sum_{B \subseteq S} g(B) = \zeta f(S)\zeta g(S)$. Compute $\zeta f$, $\zeta g$ and the Möbius transform of their pointwise product with Yates's algorithm.

## Depends on

- [Zeta and Möbius transforms on the subset lattice](../../../ComputerScience/algebraic-and-numerical-algorithms/fast-zeta-transform-and-subset-convolution/zeta-and-mobius-transforms.md)

## Proof depends on

- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](../../../ComputerScience/algebraic-and-numerical-algorithms/fast-zeta-transform-and-subset-convolution/yates-algorithm.md)

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", STOC 2007.
