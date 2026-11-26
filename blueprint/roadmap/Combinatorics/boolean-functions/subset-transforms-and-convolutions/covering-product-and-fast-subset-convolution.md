# Covering product and fast subset convolution

For $f, g$ on the subsets of an $n$-element set, the *covering product* $(f *_c g)(X) = \sum_{A \cup B = X} f(A) g(B)$ satisfies $\zeta(f *_c g) = \zeta f \cdot \zeta g$ pointwise, and the *subset convolution* $(f * g)(X) = \sum_{A \subseteq X} f(A) g(X \setminus A)$ equals the rank-$|X|$ part of the covering product of the rank-graded functions: $(f * g)(X) = \sum_{i} (f_i *_c g_{|X| - i})(X)$ with $f_i = f \cdot [|\cdot| = i]$. Hence both can be computed with $O(2^n n^2)$ ring operations (Björklund–Husfeldt–Kaski–Koivisto).

## Proof sketch

$\zeta(f *_c g)(S) = \sum_{A \cup B \subseteq S} f(A)g(B) = \zeta f(S)\zeta g(S)$. For disjoint unions, grading by size restricts covering pairs with $|A| + |B| = |X|$ to disjoint pairs. Use Yates's algorithm for each of the $n + 1$ ranks and Möbius inversion.

## Depends on

- [Zeta and Möbius transforms on the subset lattice](../../../ComputerScience/algebraic-and-numerical-algorithms/fast-zeta-transform-and-subset-convolution/zeta-and-mobius-transforms.md)

## Proof depends on

- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](../../../ComputerScience/algebraic-and-numerical-algorithms/fast-zeta-transform-and-subset-convolution/yates-algorithm.md)

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", STOC 2007.
