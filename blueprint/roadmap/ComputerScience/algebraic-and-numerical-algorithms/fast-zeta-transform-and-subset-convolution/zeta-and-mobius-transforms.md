# Zeta and Möbius transforms on the subset lattice

For a function $f : 2^{[n]} \to R$ into an abelian group, its **zeta transform** and **Möbius transform** are

$$
(\zeta f)(S) = \sum_{T \subseteq S} f(T), \qquad (\mu f)(S) = \sum_{T \subseteq S} (-1)^{|S \setminus T|} f(T).
$$

They are mutually inverse: $\mu \zeta f = \zeta \mu f = f$.

## Depends on

- [Möbius inversion formula for divisor sums](../../../NumberTheory/arithmetic-functions/multiplicative-functions/m-bius-inversion-for-arithmetic-functions/mobius-inversion.md)

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", Proceedings of the 39th ACM Symposium on Theory of Computing (STOC), 2007.
- F. Yates, "The Design and Analysis of Factorial Experiments", Imperial Bureau of Soil Science, Technical Communication 35, 1937.
