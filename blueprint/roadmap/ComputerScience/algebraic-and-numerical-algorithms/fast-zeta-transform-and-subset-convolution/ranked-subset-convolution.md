# Subset convolution and ranked zeta transforms

Let $R$ be a ring (not necessarily commutative). The **subset convolution** of $f, g : 2^{[n]} \to R$ is

$$
(f \ast g)(S) = \sum_{T \subseteq S} f(T)\, g(S \setminus T).
$$

The **ranked zeta transform** of $f$ is the family $\hat f_k = \zeta(f \cdot [|\cdot| = k])$, $k = 0, \dots, n$. Then for every $S$ with $|S| = s$,

$$
(f \ast g)(S) = \mu\Big( \sum_{k=0}^{s} \hat f_k \cdot \hat g_{s-k} \Big)(S),
$$

where products are pointwise; this is the Björklund-Husfeldt-Kaski-Koivisto fast subset convolution, computing $f \ast g$ with $O(2^n n^2)$ ring operations.

## Proof sketch

Expanding, $\mu\big(\sum_k \hat f_k\hat g_{s-k}\big)(S) = \sum_{|A| + |B| = s} f(A)g(B)\sum_{A \cup B \subseteq X \subseteq S}(-1)^{|S \setminus X|}$, and the inner sum is $[A \cup B = S]$; with $|A| + |B| = |S|$ this forces $A$ and $B$ to be disjoint with union $S$. For the running time, compute the $n + 1$ ranked zeta transforms of $f$ and of $g$ by forward Yates passes, form the pointwise rank convolutions $h_s = \sum_{k=0}^{s}\hat f_k\hat g_{s-k}$ in $O(2^n n^2)$ operations, apply an inverse Yates pass to each $h_s$, and read $(f \ast g)(S)$ from $\mu h_{|S|}$ (Björklund et al., §§2.3–2.4).

## Depends on

- [Zeta and Möbius transforms on the subset lattice](zeta-and-mobius-transforms.md)

## Proof depends on

- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](yates-algorithm.md)

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", Proceedings of the 39th ACM Symposium on Theory of Computing (STOC), 2007.
