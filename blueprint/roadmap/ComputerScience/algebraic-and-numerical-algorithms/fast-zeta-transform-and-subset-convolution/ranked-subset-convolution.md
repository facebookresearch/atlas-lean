# Subset convolution and ranked zeta transforms

The **subset convolution** of $f, g : 2^{[n]} \to R$ is

$$
(f \ast g)(S) = \sum_{T \subseteq S} f(T)\, g(S \setminus T).
$$

The **ranked zeta transform** of $f$ is the family $\hat f_k = \zeta(f \cdot [|\cdot| = k])$, $k = 0, \dots, n$. Then for every $S$ with $|S| = s$,

$$
(f \ast g)(S) = \mu\Big( \sum_{k=0}^{s} \hat f_k \cdot \hat g_{s-k} \Big)(S),
$$

where products are pointwise; this is the Björklund-Husfeldt-Kaski-Koivisto fast subset convolution, computing $f \ast g$ with $O(2^n n^2)$ ring operations.

## Depends on

- [Zeta and Möbius transforms on the subset lattice](zeta-and-mobius-transforms.md)

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", Proceedings of the 39th ACM Symposium on Theory of Computing (STOC), 2007.
