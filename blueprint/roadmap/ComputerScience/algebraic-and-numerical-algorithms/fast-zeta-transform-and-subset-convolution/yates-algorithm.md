# Yates's algorithm computes zeta and Möbius transforms in n 2^n operations

Store $f : 2^{[n]} \to R$ as a table of $2^n$ cells, cell $k$ holding the value at the set of positions of the binary digits $1$ of $k$. For $i = 0, \dots, n-1$, **pass $i$** with coefficient $c$ replaces cell $k$ by $t[k] + c\, t[k \oplus 2^i]$ whenever bit $i$ of $k$ is set. Running all $n$ passes with $c = 1$ computes $\zeta f$, and with $c = -1$ computes $\mu f$, using $n 2^{n-1}$ additions or subtractions. On the word RAM, the unsigned zeta transform of a table of naturals and the signed transforms of integer tables run in $O((n+1) 2^n)$ instructions at word sizes large enough for the total absolute sum.

## Proof sketch

After passes $0, \dots, i-1$ cell $S$ holds $\sum_T c^{|S \setminus T|} f(T)$ over the $T \subseteq S$ that agree with $S$ outside the first $i$ coordinates; pass $i$ extends the summation to coordinate $i$. For $c = 1$ this ends at $\zeta f$ and for $c = -1$ at $\mu f$.

## Depends on

- [Zeta and Möbius transforms on the subset lattice](zeta-and-mobius-transforms.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- F. Yates, "The Design and Analysis of Factorial Experiments", Imperial Bureau of Soil Science, Technical Communication 35, 1937.
- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", Proceedings of the 39th ACM Symposium on Theory of Computing (STOC), 2007.
