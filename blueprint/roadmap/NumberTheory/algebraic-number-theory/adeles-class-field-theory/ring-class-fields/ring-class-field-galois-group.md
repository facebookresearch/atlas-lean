# Galois group of a ring class field

Let $K \subset \mathbb{C}$ be an imaginary quadratic field, $\mathcal{O}$ an order in $K$ with
class group $C(\mathcal{O})$, the group of proper fractional $\mathcal{O}$-ideals (lattices
$\mathfrak{b} \subset K$ in $\mathbb{C}$ that are
[proper ideals](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/is-proper-ideal.md)
of $\mathcal{O}$) modulo principal ideals, of order the class number $h(\mathcal{O})$, and $L$ the
[ring class field](ring-class-field.md) of $\mathcal{O}$. Then $L$ is a finite Galois extension of $K$,
and there is a group isomorphism

$$\Psi \colon \mathrm{Gal}(L/K) \xrightarrow{\ \sim\ } C(\mathcal{O})$$

such that, for every $\sigma \in \mathrm{Gal}(L/K)$ with $\Psi(\sigma) = [\mathfrak{c}]$,

$$\sigma\bigl(j(\mathfrak{b})\bigr) = j(\mathfrak{c}^{-1}\mathfrak{b}) \qquad \text{for every proper fractional } \mathcal{O}\text{-ideal } \mathfrak{b}.$$

In particular $L/K$ is abelian of degree $[L : K] = h(\mathcal{O})$, and $\mathrm{Gal}(L/K)$ permutes
the values $j(\mathfrak{b})$ transitively. For $\mathcal{O} = \mathcal{O}_K$, $L$ is the Hilbert class
field $H$ of $K$ ([generation of the Hilbert class field by $j$](../hilbert-class-field/hilbert-class-field-generated-by-j.md)),
and comparing the formula with the
[Artin action on CM $j$-invariants](../hilbert-class-field/artin-action-on-cm-j-invariants.md),
$\mathrm{art}_{H/K}(\mathfrak{b})(j(\mathfrak{a})) = j(\mathfrak{b}^{-1}\mathfrak{a})$, shows that $\Psi$
is the inverse of the isomorphism from the class group onto $\mathrm{Gal}(H/K)$ induced by the Artin map.

## Expansion

A good expansion has pages for the steps of Sutherland's proof: the class group acts freely and
transitively on the values $j(\mathfrak{b})$, with $[\mathfrak{c}]$ sending $j(\mathfrak{b})$ to
$j(\mathfrak{c}^{-1}\mathfrak{b})$ through the isogeny $\mathbb{C}/\mathfrak{b} \to
\mathbb{C}/\mathfrak{c}^{-1}\mathfrak{b}$ (Lecture 20, §20.3); the action of
$\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on elliptic curves over number fields preserves
complex multiplication by $\mathcal{O}$ (Lecture 20, proof of Theorem 20.12); the compatibility
$(\mathfrak{b}E)^\sigma \simeq \mathfrak{b}^\sigma E^\sigma$ for $\sigma \in \mathrm{Gal}(L/K)$ (Lecture 20,
equation (2), whose proof the notes omit and cite from Silverman, *Advanced topics in the arithmetic of
elliptic curves*, Prop. II.2.5), which makes $\Psi$ a well-defined injective homomorphism (Lecture 20,
Theorem 20.14 and the discussion before it); every class of $C(\mathcal{O})$ contains infinitely many
ideals of prime norm (Lecture 20, Theorem 20.11); the Frobenius element $\sigma_{\mathfrak{p}}$ of an
unramified prime $\mathfrak{p}$ of $K$ in the abelian extension $L/K$ (Lecture 21, §21.1); and the
reduction modulo a prime $\mathfrak{q}$ of $L$ above such a prime, which shows that
$\Psi(\sigma_{\mathfrak{p}}) = [\mathfrak{p} \cap \mathcal{O}]$, so $\Psi$ is surjective (Lecture 21,
proof of Theorem 21.1). Each page states its result precisely, with its locator in those notes.

## Depends on

- [Ring class field of an imaginary quadratic order](ring-class-field.md)
- [Lattices that are proper ideals](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/is-proper-ideal.md)

## Proof depends on

- [Integer coefficients of the class equation of an imaginary quadratic order](class-equation-integer-coefficients.md), for $L$ being the splitting field over $K$ of a polynomial in $\mathbb{Z}[X]$, hence finite and Galois over $K$, and for the distinct values $j(\mathfrak{b})$, one for each class, on which the class group acts freely

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, [Lecture 20](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec20.pdf), §20.3 and Theorem 20.14 ($\Psi$ is a well-defined injective homomorphism compatible with
  the actions), and [Lecture 21](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec21.pdf), Theorem 21.1 ($\Psi$ is an isomorphism, the First Main Theorem of Complex
  Multiplication) and Corollary 21.2. Sutherland's $\Psi$ sends $\sigma$ to the class $\alpha_\sigma$ with
  $j(E)^\sigma = \alpha_\sigma j(E)$, and $[\mathfrak{c}]$ acts by $j(\mathfrak{b}) \mapsto
  j(\mathfrak{c}^{-1}\mathfrak{b})$ (§20.3), which gives the formula above.
- David A. Cox, *Primes of the form* $x^2 + ny^2$*: Fermat, class field theory, and complex multiplication*, 3rd ed., AMS Chelsea Publishing, Providence, RI, 2022, Lemma 9.3 and Theorem 11.1, as cited by Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [§2·1, p. 613](https://doi.org/10.1017/S0305004125101825), for
  $\mathbb{Q}(\sqrt{\Delta}, x)$ being Galois over $\mathbb{Q}(\sqrt{\Delta})$ and over $\mathbb{Q}$, with
  $\mathrm{Gal}(\mathbb{Q}(\sqrt{\Delta}, x)/\mathbb{Q}(\sqrt{\Delta})) \cong \mathrm{cl}(\Delta)$, for a singular
  modulus $x$ of discriminant $\Delta$.
- David A. Cox, *Primes of the form* $x^2 + ny^2$, Wiley, New York, 1989, Corollary 11.37, as cited by David Cox, John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull. London Math. Soc. 36 (2004), 3–12, [arXiv:math/0311202](https://arxiv.org/abs/math/0311202), §1, for the same action in a special case: for $f \in \mathbb{Q}(j)$, such as
  $f = j$, $\sigma_\beta(f(\tau_\alpha)) = f(\tau_\gamma)$ when the lattices $I_\alpha = [\tau_\alpha, 1]$,
  $I_\beta$, $I_\gamma$ attached to elliptic elements $\alpha, \beta, \gamma$ of order 2 of
  $\Gamma_0(n)^\dagger \setminus \Gamma_0(n)$ have the same order and $[I_\alpha I_\beta^{-1}] = [I_\gamma]$,
  where $\sigma_\beta$ corresponds to $[I_\beta]$ under the Artin isomorphism from $C(\mathcal{O})$ onto
  the Galois group of their ring class field, defined through class field theory.
