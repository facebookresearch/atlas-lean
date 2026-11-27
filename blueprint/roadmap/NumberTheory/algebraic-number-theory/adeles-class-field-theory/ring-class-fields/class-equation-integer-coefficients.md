# Integer coefficients of the class equation of an imaginary quadratic order

Let $K \subset \mathbb{C}$ be an imaginary quadratic field and $\mathcal{O}$ an order in $K$, with class
group $C(\mathcal{O})$, the group of proper fractional $\mathcal{O}$-ideals modulo principal ideals, of
order $h = h(\mathcal{O})$. A proper fractional $\mathcal{O}$-ideal is a lattice
$\mathfrak{a} \subset K$ in $\mathbb{C}$ that is a
[proper ideal](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/is-proper-ideal.md)
of $\mathcal{O}$, and
$j(\mathfrak{a}) = 1728\, g_2(\mathfrak{a})^3 / (g_2(\mathfrak{a})^3 - 27\, g_3(\mathfrak{a})^2)$ is its
$j$-invariant, with $g_2$ and $g_3$ the Eisenstein invariants of the lattice. Let
$\mathfrak{a}_1, \ldots, \mathfrak{a}_h$ represent the classes of $C(\mathcal{O})$. Then:

1. for proper fractional $\mathcal{O}$-ideals $\mathfrak{a}$ and $\mathfrak{b}$,
   $j(\mathfrak{a}) = j(\mathfrak{b})$ exactly when $[\mathfrak{a}] = [\mathfrak{b}]$ in
   $C(\mathcal{O})$; so $j(\mathfrak{a}_1), \ldots, j(\mathfrak{a}_h)$ are distinct, and they are all
   the values $j(\mathfrak{a})$;
2. $j(\mathfrak{a})$ is an algebraic integer for every proper fractional $\mathcal{O}$-ideal
   $\mathfrak{a}$;
3. the class equation of $\mathcal{O}$,

    $$H_{\mathcal{O}}(X) = \prod_{i=1}^{h} \bigl(X - j(\mathfrak{a}_i)\bigr),$$

    has coefficients in $\mathbb{Z}$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- lattices with the same $j$-invariant are [homothetic](../../../../Analysis/special-functions/elliptic-functions/homothetic-complex-period-lattices/is-homothetic.md),
  and two proper fractional $\mathcal{O}$-ideals are homothetic exactly when they lie in the same class,
  so $C(\mathcal{O})$ acts freely and transitively on the values $j(\mathfrak{a})$ (Sutherland, Lecture 20,
  recalled in §20.3);
- the modular polynomial $\Phi_N \in \mathbb{Z}[X, Y]$ (Lecture 19, Theorem 19.17), and Theorem 20.3:
  $\Phi_N(j_1, j_2) = 0$ exactly when $j_1$ and $j_2$ are the $j$-invariants of curves related by a
  cyclic isogeny of degree $N$;
- the leading term $-X^{2p}$ of $\Phi_p(X, X)$ for $p$ prime (Lemma 20.9);
- every class of $C(\mathcal{O})$ contains infinitely many ideals of prime norm (Theorem 20.11), so there
  is a principal $\mathcal{O}$-ideal of prime norm $p$, which makes $j(\mathfrak{a})$ a root of the monic
  integer polynomial $-\Phi_p(X, X)$ (proof of Theorem 20.12 and Corollary 20.13);
- the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on elliptic curves over
  $\overline{\mathbb{Q}}$ preserves complex multiplication by $\mathcal{O}$ and so permutes the values
  $j(\mathfrak{a})$, whence the coefficients of $H_{\mathcal{O}}$ are rational algebraic integers (proof
  of Theorem 20.12).

Each page states its result precisely, with its locator in those notes.

## Depends on

- [Lattices that are proper ideals](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/is-proper-ideal.md)

## Proof depends on

- [Homothetic period pairs](../../../../Analysis/special-functions/elliptic-functions/homothetic-complex-period-lattices/is-homothetic.md), for homothety of lattices

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, [Lecture 19](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec19.pdf), Theorem 19.17 ($\Phi_N \in \mathbb{Z}[X, Y]$), and [Lecture 20](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec20.pdf), §20.3 (the free and transitive action of $C(\mathcal{O})$ on the
  $j$-invariants of the curves with complex multiplication by $\mathcal{O}$, which are the tori
  $\mathbb{C}/\mathfrak{b}$ for proper $\mathcal{O}$-ideals $\mathfrak{b}$), Theorem 20.12 (integer
  coefficients) with its proof, and Corollary 20.13 (integrality of $j$).
- David A. Cox, *Primes of the form* $x^2 + ny^2$*: Fermat, class field theory, and complex multiplication*, 3rd ed., AMS Chelsea Publishing, Providence, RI, 2022, Theorem 11.1 and Proposition 13.2, as cited by Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [§2·1, p. 613](https://doi.org/10.1017/S0305004125101825), for
  $H_\Delta(z) = \prod_{i=1}^{n} (z - x_i) \in \mathbb{Z}[z]$, the product over all the distinct singular
  moduli $x_1, \ldots, x_n$ of discriminant $\Delta$.
