# Galois group of a ring class field

Let $K \subset \mathbb{C}$ be an imaginary quadratic field, $\mathcal{O}$ an order in $K$ with
class group $C(\mathcal{O})$, the group of proper fractional $\mathcal{O}$-ideals modulo principal
ideals, of order the class number $h(\mathcal{O})$, and $L$ the
[ring class field](ring-class-field.md) of $\mathcal{O}$. Then $L$ is a finite Galois extension of $K$,
and there is a group isomorphism

$$\Psi \colon \mathrm{Gal}(L/K) \xrightarrow{\ \sim\ } C(\mathcal{O})$$

such that, for every $\sigma \in \mathrm{Gal}(L/K)$ with $\Psi(\sigma) = [\mathfrak{c}]$,

$$\sigma\bigl(j(\mathfrak{b})\bigr) = j(\mathfrak{c}^{-1}\mathfrak{b}) \qquad \text{for every proper fractional } \mathcal{O}\text{-ideal } \mathfrak{b}.$$

In particular $L/K$ is abelian of degree $[L : K] = h(\mathcal{O})$, and $\mathrm{Gal}(L/K)$ permutes
the values $j(\mathfrak{b})$ transitively. For $\mathcal{O} = \mathcal{O}_K$ the isomorphism is the
inverse of the Artin map of the Hilbert class field, by the
[Artin action on CM $j$-invariants](../hilbert-class-field/artin-action-on-cm-j-invariants.md).

## Expansion

A good expansion has pages for the steps of Sutherland's proof: the action of
$\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on elliptic curves preserves complex multiplication
by $\mathcal{O}$, so it permutes the values $j(\mathfrak{b})$ (Lecture 20, proof of Theorem 20.12); the
compatibility $(\mathfrak{b}E)^\sigma \simeq \mathfrak{b}^\sigma E^\sigma$, which makes $\Psi$ a
well-defined injective homomorphism (Lecture 20, Theorem 20.14); every class of $C(\mathcal{O})$
contains infinitely many ideals of prime norm (Lecture 20, Theorem 20.11); and the reduction modulo a
prime $\mathfrak{q}$ of $L$ above such an ideal $\mathfrak{p}$, which shows that the Frobenius element
of $\mathfrak{p}$ maps to $[\mathfrak{p} \cap \mathcal{O}]$, so $\Psi$ is surjective (Lecture 21, proof
of Theorem 21.1). Each page states its result precisely, with its locator in those notes.

## Depends on

- [Ring class field of an imaginary quadratic order](ring-class-field.md)

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, [Lecture 20](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec20.pdf), Theorem 20.14 ($\Psi$ is a well-defined injective homomorphism compatible with the
  actions), and [Lecture 21](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec21.pdf), Theorem 21.1 ($\Psi$ is an isomorphism, the first main theorem of complex
  multiplication) and Corollary 21.2.
- David A. Cox, *Primes of the form* $x^2 + ny^2$*: Fermat, class field theory, and complex multiplication*, 3rd ed., AMS Chelsea Publishing, Providence, RI, 2022, Lemma 9.3 and Theorem 11.1, as cited by Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [§2·1, p. 613](https://doi.org/10.1017/S0305004125101825), for
  $\mathrm{Gal}(\mathbb{Q}(\sqrt{\Delta}, x)/\mathbb{Q}(\sqrt{\Delta})) \cong \mathrm{cl}(\Delta)$ for a singular
  modulus $x$ of discriminant $\Delta$.
- David A. Cox, *Primes of the form* $x^2 + ny^2$, Wiley, New York, 1989, Corollary 11.37, as cited by David Cox, John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull. London Math. Soc. 36 (2004), 3–12, [arXiv:math/0311202](https://arxiv.org/abs/math/0311202), §1, for the same action through the Artin isomorphism
  $C(\mathcal{O}) \cong \mathrm{Gal}(L/K)$: $\sigma_\beta(j(\tau_\alpha)) = j(\tau_\gamma)$ when
  $[I_\alpha I_\beta^{-1}] = [I_\gamma]$.
