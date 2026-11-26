# Pairing adjoint kernel

Let $P$ be a finite abelian group and $K$ a field, and let $e : P \times P \to K^\times$ satisfy:

- $e(x + x', y) = e(x, y) \, e(x', y)$ and $e(x, y + y') = e(x, y) \, e(x, y')$ for all $x, x', y, y'$;
- nondegeneracy: if $e(x, y) = 1$ for all $y$ then $x = 0$, and if $e(x, y) = 1$ for all $x$ then $y = 0$;
- every homomorphism $\chi : P \to K^\times$ has the form $\chi(x) = e(x, y)$ for some $y \in P$.

Let $T, T' : P \to P$ be group endomorphisms that are adjoint for $e$: $e(T x, y) = e(x, T' y)$ for all $x, y \in P$. Then

$$\lvert \ker T \rvert = \lvert \ker T' \rvert.$$
