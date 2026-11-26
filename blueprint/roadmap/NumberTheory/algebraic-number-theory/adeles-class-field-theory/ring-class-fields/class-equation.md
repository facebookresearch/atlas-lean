# The class equation of an imaginary quadratic order

Let $K \subset \mathbb{C}$ be an imaginary quadratic field and $\mathcal{O}$ an order in $K$, with class
group $C(\mathcal{O})$ of order $h = h(\mathcal{O})$, and let $\mathfrak{a}_1, \ldots, \mathfrak{a}_h$
represent the classes of $C(\mathcal{O})$; each is a lattice in $\mathbb{C}$ that is a
[proper ideal](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/is-proper-ideal.md) of $\mathcal{O}$. With
$j(\mathfrak{a}) = 1728\, g_2(\mathfrak{a})^3 / (g_2(\mathfrak{a})^3 - 27\, g_3(\mathfrak{a})^2)$ the
$j$-invariant of a lattice, the class equation of $\mathcal{O}$ is

$$H_{\mathcal{O}}(X) = \prod_{i=1}^{h} \bigl(X - j(\mathfrak{a}_i)\bigr).$$

Then $j(\mathfrak{a}_1), \ldots, j(\mathfrak{a}_h)$ are distinct, $H_{\mathcal{O}}$ has coefficients in
$\mathbb{Z}$, and $H_{\mathcal{O}}$ is irreducible over $K$ and over $\mathbb{Q}$. Hence for every proper
fractional $\mathcal{O}$-ideal $\mathfrak{a}$, $H_{\mathcal{O}}$ is the minimal polynomial of
$j(\mathfrak{a})$ over $\mathbb{Q}$ and over $K$, and

$$[\mathbb{Q}(j(\mathfrak{a})) : \mathbb{Q}] = [K(j(\mathfrak{a})) : K] = h(\mathcal{O}).$$

The values are distinct because two lattices have the same $j$-invariant exactly when they are homothetic,
and two proper ideals are homothetic exactly when they lie in the same class. The coefficients are
algebraic integers fixed by $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, which permutes the roots, so
they are integers. Irreducibility over $K$ comes from the transitive action of the
[Galois group of the ring class field](ring-class-field-galois-group.md) on the roots, and a factorization
over $\mathbb{Q}$ would be one over $K$.

## Depends on

- [Lattices that are proper ideals](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/is-proper-ideal.md)

## Proof depends on

- [Galois group of a ring class field](ring-class-field-galois-group.md), for the transitive action on the roots and the permutation of the roots by $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$
- [The j-invariant of a proper ideal generates the ring class field](j-generates-ring-class-field.md), for the integrality of the roots

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, [Lecture 20](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec20.pdf), Theorem 20.12 (integer coefficients), and [Lecture 21](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec21.pdf), Corollary 21.2 (irreducibility over
  $K$, and $[K(j(\mathfrak{a})) : K] = h(\mathcal{O})$).
- David A. Cox, *Primes of the form* $x^2 + ny^2$*: Fermat, class field theory, and complex multiplication*, 3rd ed., AMS Chelsea Publishing, Providence, RI, 2022, Theorem 11.1 and Proposition 13.2, as cited by Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [§2·1, p. 613](https://doi.org/10.1017/S0305004125101825), for $H_\Delta \in \mathbb{Z}[z]$
  irreducible over $\mathbb{Q}$ and over $\mathbb{Q}(\sqrt{\Delta})$, from which Fowler deduces
  $[\mathbb{Q}(x) : \mathbb{Q}] = [\mathbb{Q}(\sqrt{\Delta}, x) : \mathbb{Q}(\sqrt{\Delta})] = h(\Delta)$ for a
  singular modulus $x$ of discriminant $\Delta$.
- David A. Cox, *Primes of the form* $x^2 + ny^2$, Wiley, New York, 1989, Proposition 13.2, as cited by Yuri Bilu, Florian Luca and Amalia Pizarro-Madariaga, *Rational products of singular moduli*, J. Number Theory 158 (2016), 397–410, [arXiv:1410.1806](https://arxiv.org/abs/1410.1806), proof of Proposition 2.5 (numbered as in the arXiv
  version), for the conjugates of $j(\tau)$ being the values $j(\mathfrak{a})$, $[\mathfrak{a}] \in C(\mathcal{O})$.
