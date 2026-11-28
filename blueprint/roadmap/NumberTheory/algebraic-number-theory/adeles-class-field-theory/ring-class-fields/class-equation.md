# Irreducibility of the class equation of an imaginary quadratic order

Let $K \subset \mathbb{C}$ be an imaginary quadratic field, $\mathcal{O}$ an order in $K$ with class
number $h(\mathcal{O})$, and $H_{\mathcal{O}} \in \mathbb{Z}[X]$ the class equation of $\mathcal{O}$,
the monic polynomial whose roots are the $h(\mathcal{O})$ distinct $j$-invariants of the classes of
proper fractional $\mathcal{O}$-ideals
([integer coefficients of the class equation](class-equation-integer-coefficients.md)). Then
$H_{\mathcal{O}}$ is irreducible over $K$ and over $\mathbb{Q}$. Hence for every proper fractional
$\mathcal{O}$-ideal $\mathfrak{a}$, that is, every lattice $\mathfrak{a} \subset K$ in $\mathbb{C}$ that
is a [proper ideal](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/is-proper-ideal.md)
of $\mathcal{O}$, $H_{\mathcal{O}}$ is the minimal polynomial of $j(\mathfrak{a})$ over $\mathbb{Q}$
and over $K$, and

$$[\mathbb{Q}(j(\mathfrak{a})) : \mathbb{Q}] = [K(j(\mathfrak{a})) : K] = h(\mathcal{O}).$$

The roots of $H_{\mathcal{O}}$ are distinct and lie in the
[ring class field](ring-class-field.md) $L$, and $\mathrm{Gal}(L/K)$ permutes them transitively
([Galois group of the ring class field](ring-class-field-galois-group.md)), so the monic polynomial
$H_{\mathcal{O}} \in K[X]$ is irreducible over $K$. A factorization over $\mathbb{Q}$ would be one over
$K$, so $H_{\mathcal{O}}$ is irreducible over $\mathbb{Q}$ too.

## Depends on

- [Integer coefficients of the class equation of an imaginary quadratic order](class-equation-integer-coefficients.md)
- [Lattices that are proper ideals](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/is-proper-ideal.md)

## Proof depends on

- [Integer coefficients of the class equation of an imaginary quadratic order](class-equation-integer-coefficients.md), for $H_{\mathcal{O}} \in \mathbb{Z}[X]$, its $h(\mathcal{O})$ distinct roots, and $j(\mathfrak{a})$ being one of them
- [Galois group of a ring class field](ring-class-field-galois-group.md), for $L/K$ Galois and the transitive action of $\mathrm{Gal}(L/K)$ on the roots

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, [Lecture 21](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec21.pdf), Corollary 21.2 (irreducibility over $K$, and
  $\mathrm{Gal}(K(j(E))/K) \simeq C(\mathcal{O})$) and its proof.
- David A. Cox, *Primes of the form* $x^2 + ny^2$*: Fermat, class field theory, and complex multiplication*, 3rd ed., AMS Chelsea Publishing, Providence, RI, 2022, Theorem 11.1 and Proposition 13.2, as cited by Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [§2·1, p. 613](https://doi.org/10.1017/S0305004125101825), for $H_\Delta \in \mathbb{Z}[z]$
  irreducible over $\mathbb{Q}$ and over $\mathbb{Q}(\sqrt{\Delta})$, from which Fowler deduces
  $[\mathbb{Q}(x) : \mathbb{Q}] = [\mathbb{Q}(\sqrt{\Delta}, x) : \mathbb{Q}(\sqrt{\Delta})] = h(\Delta)$ for a
  singular modulus $x$ of discriminant $\Delta$.
- David A. Cox, *Primes of the form* $x^2 + ny^2$, Wiley, New York, 1989, Proposition 13.2, as cited by Yuri Bilu, Florian Luca and Amalia Pizarro-Madariaga, *Rational products of singular moduli*, J. Number Theory 158 (2016), 397–410, [arXiv:1410.1806](https://arxiv.org/abs/1410.1806), proof of Proposition 2.5 (numbered as in the arXiv
  version), for the set of conjugates of $j(\tau)$ being $\{j(\mathcal{A}) : \mathcal{A} \in \mathrm{Cl}(\mathcal{O})\}$.
