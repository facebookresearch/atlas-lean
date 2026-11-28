# Main theorem of complex multiplication for elliptic curves

Let $K \subset \mathbb{C}$ be an imaginary quadratic field and $\overline{\mathbb{Q}}$ the algebraic
closure of $\mathbb{Q}$ in $\mathbb{C}$. Let $A$ be an elliptic curve over $\overline{\mathbb{Q}}$ with
complex multiplication by $K$: an embedding $K \to \mathrm{End}(A) \otimes \mathbb{Q}$, normalised so
that each $a \in K$ acts on the tangent space of $A$ at the origin as multiplication by $a$. Let
$T_f(A) = \prod_\ell T_\ell(A)$ be its total Tate module and $V_f(A) = T_f(A) \otimes_{\mathbb{Z}} \mathbb{Q}$,
a free module of rank one over the finite adèles $\mathbb{A}_{f,K} = K \otimes_{\mathbb{Q}} \mathbb{A}_f$
of $K$. Let $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/K)$ and let $s \in \mathbb{A}_{f,K}^\times$
be a finite idèle whose image under the global Artin map of $K$ is the restriction of $\sigma$ to the
maximal abelian extension $K^{\mathrm{ab}}$ (as $K$ is totally imaginary, the Artin map factors through
the finite idèles). Then there is a unique quasi-isogeny $\alpha \colon A \to \sigma A$, that is, an
invertible element of $\mathrm{Hom}(A, \sigma A) \otimes \mathbb{Q}$, commuting with the actions of $K$,
such that

$$\alpha(s^{-1} x) = \sigma(x) \qquad \text{for all } x \in V_f(A),$$

where $\sigma \colon V_f(A) \to V_f(\sigma A)$ is induced by the action of $\sigma$ on torsion points.
As the torsion points of $A$ form $V_f(A) / T_f(A)$, this describes the action of $\sigma$ on the
torsion points of $A$ through the idèle $s$.

Milne states the theorem for abelian varieties with complex multiplication by a CM-algebra $E$ of
CM-type $\Phi$, for $\sigma$ fixing the reflex field $E^*$, as
$\alpha(N_\Phi(s') \cdot x) = \sigma x$ for $s'$ with $\mathrm{art}_{E^*}(s') = \sigma|_{E^{*\mathrm{ab}}}$,
where $N_\Phi$ is the reflex norm and $\mathrm{art} = \mathrm{rec}^{-1}$ is the reciprocal of the usual
Artin map $\mathrm{rec}$: for the idèle $a$ that is a uniformizer at one finite place $v$ and $1$
elsewhere, $\mathrm{art}(a)$ lies in the decomposition group at $v$, and its image in the unramified
quotient of that group, the Galois group of the maximal unramified extension of the completion at $v$,
is the inverse of the arithmetic Frobenius. For an elliptic curve normalised as
above, $E = K$, $\Phi$ is the inclusion $K \subset \overline{\mathbb{Q}}$, the reflex field is $K$ and
$N_\Phi$ is the identity, since by Milne's definition $N_\Phi(a)$ is the determinant of multiplication
by $a$ on a one-dimensional $K$-vector space; with $s = s'^{-1}$ this is the statement above. (This
specialization is worked out here, not in Milne's text.)

The theorem strengthens the [Artin action on $j$-invariants](artin-action-on-cm-j-invariants.md),
which describes the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/K)$ on the isomorphism classes of the
curves alone. Milne derives it from the fundamental theorem in terms of ideals (his Section 9), proved
by reduction modulo primes with the Shimura–Taniyama formula (Section 8), and from class field theory,
which relates idèles to ray class groups.

## Depends on

- [Global Artin map](../reciprocity-law/global-artin-map.md), for the global Artin map of $K$, trivial on the infinite idèles of the totally imaginary field $K$

## Proof depends on

- [Global reciprocity law](../reciprocity-law/global-reciprocity-law.md), through which Milne's proof passes between idèles and ray class groups

## Sources

- J. S. Milne, *Complex Multiplication*, version 0.10 (2020),
  <https://www.jmilne.org/math/CourseNotes/CM.pdf>, Section 9: Theorem 9.10 (the fundamental theorem in
  terms of idèles) and its proof; the review of the reflex norm at the start of Section 9; the
  convention $\mathrm{art}_k(s) = \mathrm{rec}_k(s)^{-1}$, stated immediately before Lemma 9.4 and
  described at the start of Section 10 (a prime element corresponds to the inverse of the arithmetic
  Frobenius).
- J. S. Milne, *The fundamental theorem of complex multiplication*, arXiv:0705.3446v1 (2007),
  Theorem 3.10 (the same theorem, for $\sigma$ fixing the reflex field).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses an analytic form of this result, for curves $\mathbb{C}/\mathfrak{a}$ with
  $\mathfrak{a}$ a fractional ideal, as `GroundTheory.Global.Elliptic.main_theorem_complexMultiplication`.
