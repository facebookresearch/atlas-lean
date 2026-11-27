# Zeta and Möbius transforms on the subset lattice

For a function $f : 2^{[n]} \to R$ into an abelian group, its **zeta transform** and **Möbius transform** are

$$
(\zeta f)(S) = \sum_{T \subseteq S} f(T), \qquad (\mu f)(S) = \sum_{T \subseteq S} (-1)^{|S \setminus T|} f(T).
$$

They are mutually inverse: $\mu \zeta f = \zeta \mu f = f$.

## Proof sketch

Both composites equal $\sum_{T \subseteq S} f(T) \sum_{T \subseteq U \subseteq S} (-1)^{|S \setminus U|}$, and the inner sum is $(1 - 1)^{|S \setminus T|} = [T = S]$ by the binomial theorem.

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", Proceedings of the 39th ACM Symposium on Theory of Computing (STOC), 2007.
- F. Yates, "The Design and Analysis of Factorial Experiments", Imperial Bureau of Soil Science, Technical Communication 35, 1937.
