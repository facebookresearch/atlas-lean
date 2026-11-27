# Merkl's bound for the Arakelov–Green function

This node is still to be broken down. Let $X$ be a compact connected Riemann surface of positive
genus, with [Arakelov $(1,1)$-form](arakelov-green-function.md) $\mu$ and Arakelov–Green function
$\mathrm{gr}_X$. A **Merkl atlas** for $X$ is a quadruple $(\{(U_j, z_j)\}_{j=1}^n, r_1, M, c_1)$,
where $\{(U_j, z_j)\}_{j=1}^n$ is a finite atlas for $X$ and $\frac12 < r_1 < 1$, $M \ge 1$ and
$c_1 > 0$ are real numbers, such that:

1. each $z_j U_j$ is the open unit disc;
2. the open sets $U_j^{r_1} := \{x \in U_j : \lvert z_j(x) \rvert < r_1\}$, $1 \le j \le n$,
   cover $X$;
3. for all $1 \le j, j' \le n$, the function $\lvert dz_j / dz_{j'} \rvert$ on $U_j \cap U_{j'}$
   is bounded above by $M$;
4. for $1 \le j \le n$, writing $\mu = i F_j \, dz_j \wedge d\overline{z_j}$ on $U_j$, one has
   $0 \le F_j(x) \le c_1$ for all $x \in U_j$.

**Theorem (Merkl).** Let $(\{(U_j, z_j)\}_{j=1}^n, r_1, M, c_1)$ be a Merkl atlas for $X$. Then

$$\sup_{(X \times X) \setminus \Delta} \mathrm{gr}_X \le \frac{330 \, n}{(1 - r_1)^{3/2}} \log
\frac{1}{1 - r_1} + 13.2 \, n c_1 + (n - 1) \log M.$$

Furthermore, for every index $j$ and all $x \ne y$ in $U_j^{r_1}$,

$$\bigl\lvert \mathrm{gr}_X(x, y) - \log \lvert z_j(x) - z_j(y) \rvert \bigr\rvert \le \frac{330 \,
n}{(1 - r_1)^{3/2}} \log \frac{1}{1 - r_1} + 13.2 \, n c_1 + (n - 1) \log M.$$

Merkl proved the bound without explicit constants and without the dependence on $r_1$; the
explicit form is Bruin's.

## Depends on

- [Arakelov $(1,1)$-form and Arakelov–Green function](arakelov-green-function.md)

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion follows Bruin's appendix: the functions $g_{a,b}$ and $g_{a,\mu}$ with
$2\pi g_{a,\mu}(b) = \mathrm{gr}_\mu(a, b)$ (p. 127); Lemma A.1, on real harmonic functions on the
annulus $U^{r_4} \setminus U^{r_2}$ of a chart (p. 128); the smooth functions $\tilde g_{a,b}$ of Lemma A.2
(p. 129); the bounds
of Lemmas A.3, A.4 and A.5 (pp. 130, 133 and 135); and the assembly with a partition of unity
subordinate to the cover $\{U_j^{r_1}\}$ and the choice $r_2 = 0.39 + 0.61 r_1$ (pp. 136–137).

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, Definition 3.1.1 and Theorem 3.1.2, pp. 104–105.
- P. Bruin, *Appendix: Merkl's method of bounding Green functions*, in A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, pp. 126–137, <https://doi.org/10.2140/ant.2014.8.89>, proof of Theorem 3.1.2, pp. 126–137.
- F. Merkl, *An upper bound for Green functions on Riemann surfaces*, in *Computational aspects of
  modular forms and Galois representations*, Ann. of Math. Stud. 176, Princeton Univ. Press, 2011,
  203–215, Theorem 10.1, as cited by Javanpeykar, p. 104 (not read here).
