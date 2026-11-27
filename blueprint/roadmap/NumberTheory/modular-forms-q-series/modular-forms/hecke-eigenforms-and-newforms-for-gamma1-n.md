# Hecke eigenforms and newforms for Γ₁(N)

This node is still to be broken down. It covers the cusp forms that Galois representations are attached
to. For integers $N \ge 1$ and $k$, let $S_k(\Gamma_1(N))$ be the space of [cusp forms](cusp-form.md) of weight $k$
for [$\Gamma_1(N)$](congruence-subgroup-gamma1.md), with $q$-expansions $f = \sum_{n \ge 1} a_n(f) q^n$, $q = e^{2\pi i \tau}$, and with its Hecke
operators $T_n$ ($n \ge 1$) and diamond operators $\langle d \rangle$ ($d \in (\mathbb{Z}/N\mathbb{Z})^\times$),
which commute. For a Dirichlet character $\varepsilon$ modulo $N$, $S_k(N, \varepsilon)$ is the subspace on which
each $\langle d \rangle$ acts as $\varepsilon(d)$.

- A **cuspidal eigenform** for the Hecke operators away from the level is a nonzero $f \in S_k(\Gamma_1(N))$ that
  is an eigenvector of $T_\ell$ for every prime $\ell \nmid N$; its eigenvalues $a_\ell$, $T_\ell f = a_\ell f$,
  are its Hecke eigenvalues.
- For positive integers $d$ and $M$ with $dM \mid N$, the map $f \mapsto f|[\iota_d]_k$, $f|[\iota_d]_k(z) = d^{k-1} f(dz)$,
  sends $S_k(\Gamma_1(M))$ injectively into $S_k(\Gamma_1(N))$. The **old subspace** $S_k(\Gamma_1(N))^{\mathrm{old}}$ is
  the span of the images of these maps with $M \ne N$, and the **new subspace** $S_k(\Gamma_1(N))^{\mathrm{new}}$ is its
  orthogonal complement for the Petersson inner product, which is positive definite on cusp forms; so
  $S_k(\Gamma_1(N)) = S_k(\Gamma_1(N))^{\mathrm{new}} \oplus S_k(\Gamma_1(N))^{\mathrm{old}}$. Both are stable under the
  Hecke operators prime to $N$, and the new subspace under every $T_n$.
- A **newform** of weight $k$ and level $N$ is an $f \in S_k(\Gamma_1(N))^{\mathrm{new}}$ that is an eigenvector of
  every $T_n$ and normalized by $a_1(f) = 1$. Then $T_n f = a_n(f) f$ for every $n$; $f$ lies in
  $S_k(N, \varepsilon)$ for a Dirichlet character $\varepsilon$ modulo $N$, unique since $\langle d \rangle f = \varepsilon(d) f$,
  its nebentypus; and the field $\mathbb{Q}(a_n(f) : n \ge 1) \subset \mathbb{C}$ is a number field.

A good expansion has pages for: the $q$-expansions of the [cusp forms](cusp-form.md) for $\Gamma_1(N)$; the
Hecke operators $T_n$ and $\langle d \rangle$ on them in every weight $k$, as double coset operators for the
weight-$k$ action, extending the [Hecke operators $T_n$ on weight-two cusp forms for a group of level
$N$](hecke-operators-of-level-n.md) to every weight, and their commutativity; the decomposition by nebentypus; the Petersson inner product on cusp forms and the adjointness
of the Hecke operators prime to the level; the degeneracy maps and the old and new subspaces; and the theorem
of Atkin, Lehner and Li that the newforms form a basis of the new subspace, are determined by their Hecke
eigenvalues at almost all primes, and that every eigenvalue system away from the level of a cuspidal
eigenform is that of a newform of a level dividing $N$.

## Depends on

- [Cusp form](cusp-form.md), for $S_k(\Gamma_1(N))$
- [Congruence subgroup $\Gamma_1(N)$](congruence-subgroup-gamma1.md)
- [Hecke operator](hecke-operators/hecke-operator.md), for the Hecke operators as double coset operators

## Proof depends on

Its proof uses the inputs listed in the expansion note.

## Sources

- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference Proceedings
  17 (1995): §3.6 ("The Petersson inner product is positive definite on the space of cusp forms"); §6.1 (the maps
  $\iota^*_{d,M,N} \colon f \mapsto f|[\iota_d]_k = d^{k-1} f(dz)$, (6.1.1); "the linear span of the images of the maps
  $\iota^*_{d,M,N}$ over all $d, M$ with $dM \mid N$, $M \ne N$, is called the old subspace of $S_k(\Gamma_1(N))$ [...]. We
  define the new subspace of $S_k(\Gamma_1(N))$, denoted $S_k(\Gamma_1(N))^{\mathrm{new}}$, as the orthogonal complement
  of $S_k(\Gamma_1(N))^{\mathrm{old}}$ in $S_k(\Gamma_1(N))$ with respect to the Petersson inner product", both stable under
  the Hecke operators prime to $N$); §6.3 (Corollary 6.3.1 and the stability of the new subspace under the full Hecke ring; "A
  normalized eigenform in $S_k(\Gamma_1(N))^{\mathrm{new}}$ is called a newform (or a primitive cusp form) of level $N$").
- W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics 79, American
  Mathematical Society (2007), author's version <https://wstein.org/books/modform/stein-modform.pdf>: Definition 9.9, p. 164 ("A newform is a $\mathbb{T}$-eigenform $f \in S_k(\Gamma_1(N))^{\mathrm{new}}$
  that is normalized so that the coefficient of $q$ is $1$") and Proposition 9.10 ($T_n f = a_n f$ for a
  normalized eigenvector of all $T_n$ in $M_k(N, \varepsilon)$); Remark 9.11, p. 164 (the diamond operators lie in
  the Hecke algebra, "Thus any $\mathbb{T}$-eigenform in $M_k(\Gamma_1(N))$ lies in a subspace $M_k(N, \varepsilon)$ for some
  Dirichlet character $\varepsilon$").
- K. Kato, "p-adic Hodge theory and values of zeta functions of modular forms", Astérisque 295 (2004),
  117–290, <https://www.numdam.org/item/AST_2004__295__117_0.pdf>: §6.3, p. 161 (for a normalized newform $f$,
  "$F = \mathbb{Q}(a_n ; n \ge 1) \subset \mathbb{C}$. Then $F$ is a finite extension of $\mathbb{Q}$").
