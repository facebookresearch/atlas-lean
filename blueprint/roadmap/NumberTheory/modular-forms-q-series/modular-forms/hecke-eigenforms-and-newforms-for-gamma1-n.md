# Hecke eigenforms and newforms for Γ₁(N)

This node is still to be broken down. It covers the cusp forms that Galois representations are attached
to. For integers $N \ge 1$ and $k$, let $S_k(\Gamma_1(N))$ be the space of cusp forms of weight $k$ for
$\Gamma_1(N)$, with $q$-expansions $f = \sum_{n \ge 1} a_n(f) q^n$, $q = e^{2\pi i \tau}$, and with its Hecke
operators $T_n$ ($n \ge 1$) and diamond operators $\langle d \rangle$ ($d \in (\mathbb{Z}/N\mathbb{Z})^\times$),
which commute. For a Dirichlet character $\varepsilon$ modulo $N$, $S_k(N, \varepsilon)$ is the subspace on which
each $\langle d \rangle$ acts as $\varepsilon(d)$.

- A **cuspidal eigenform** for the Hecke operators away from the level is a nonzero $f \in S_k(\Gamma_1(N))$ that
  is an eigenvector of $T_\ell$ for every prime $\ell \nmid N$; its eigenvalues $a_\ell$, $T_\ell f = a_\ell f$,
  are its Hecke eigenvalues.
- For a divisor $M$ of $N$ and a divisor $t$ of $N/M$, the degeneracy map
  $\alpha_t \colon S_k(\Gamma_1(M)) \to S_k(\Gamma_1(N))$ sends $f(q)$ to $f(q^t)$. The **old subspace**
  $S_k(\Gamma_1(N))^{\mathrm{old}}$ is the sum of the images of the $\alpha_t$ with $M \ne N$, and the **new
  subspace** $S_k(\Gamma_1(N))^{\mathrm{new}}$ is the intersection of the kernels of the maps
  $\beta_t \colon S_k(\Gamma_1(N)) \to S_k(\Gamma_1(M))$ in the other direction, $M \ne N$ (Stein refers to Lang,
  Chapter VIII, for them). Both are stable under the $T_n$, and the Petersson inner product shows
  $S_k(\Gamma_1(N)) = S_k(\Gamma_1(N))^{\mathrm{new}} \oplus S_k(\Gamma_1(N))^{\mathrm{old}}$.
- A **newform** of weight $k$ and level $N$ is an $f \in S_k(\Gamma_1(N))^{\mathrm{new}}$ that is an eigenvector of
  every $T_n$ and normalized by $a_1(f) = 1$. Then $T_n f = a_n(f) f$ for every $n$; $f$ lies in
  $S_k(N, \varepsilon)$ for a Dirichlet character $\varepsilon$ modulo $N$, unique since $\langle d \rangle f = \varepsilon(d) f$,
  its nebentypus; and the field $\mathbb{Q}(a_n(f) : n \ge 1) \subset \mathbb{C}$ is a number field.

A good expansion has pages for: cusp forms for $\Gamma_1(N)$ and their $q$-expansions; the Hecke operators
$T_n$ and $\langle d \rangle$ on them, as double coset operators for the weight-$k$ action, and their
commutativity; the decomposition by nebentypus; the Petersson inner product on cusp forms and the adjointness
of the Hecke operators prime to the level; the degeneracy maps and the old and new subspaces; and the theorem
of Atkin, Lehner and Li that the newforms form a basis of the new subspace, are determined by their Hecke
eigenvalues at almost all primes, and that every eigenvalue system away from the level of a cuspidal
eigenform is that of a newform of a level dividing $N$.

## Depends on

- [Hecke operator](hecke-operators/hecke-operator.md), for the Hecke operators as double coset operators

## Sources

- W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics 79, American
  Mathematical Society (2007), author's version <https://wstein.org/books/modform/stein-modform.pdf>: §9.2,
  pp. 161–162 (the degeneracy maps $\alpha_t$ and the maps $\beta_t$ in the other direction, the old subspace, the
  new subspace as the intersection of the kernels of the $\beta_t$, and, "One can use the Petersson inner product to
  show",
  $S_k(\Gamma_1(N)) = S_k(\Gamma_1(N))^{\mathrm{new}} \oplus S_k(\Gamma_1(N))^{\mathrm{old}}$, stable under the Hecke
  operators), Definition 9.9, p. 164 ("A newform is a $\mathbb{T}$-eigenform $f \in S_k(\Gamma_1(N))^{\mathrm{new}}$
  that is normalized so that the coefficient of $q$ is $1$") and Proposition 9.10 ($T_n f = a_n f$ for a
  normalized eigenvector of all $T_n$ in $M_k(N, \varepsilon)$); Remark 9.11, p. 164 (the diamond operators lie in
  the Hecke algebra, "Thus any $\mathbb{T}$-eigenform in $M_k(\Gamma_1(N))$ lies in a subspace $M_k(N, \varepsilon)$ for some
  Dirichlet character $\varepsilon$").
- K. Kato, "p-adic Hodge theory and values of zeta functions of modular forms", Astérisque 295 (2004),
  117–290, <https://www.numdam.org/item/AST_2004__295__117_0.pdf>: §6.3, p. 161 (for a normalized newform $f$,
  "$F = \mathbb{Q}(a_n ; n \ge 1) \subset \mathbb{C}$. Then $F$ is a finite extension of $\mathbb{Q}$").
