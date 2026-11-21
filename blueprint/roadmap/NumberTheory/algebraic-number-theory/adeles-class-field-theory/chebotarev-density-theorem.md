# Chebotarev density theorem

Let $L/K$ be a finite Galois extension of number fields with Galois group $G$, and let $C \subseteq G$
be stable under conjugation. For a nonzero prime ideal $\mathfrak{p}$ of $\mathcal{O}_K$ unramified in
$L$, the Frobenius elements of the primes $\mathfrak{P}$ of $\mathcal{O}_L$ above $\mathfrak{p}$, the
elements $\sigma \in G$ with $\sigma(\mathfrak{P}) = \mathfrak{P}$ and
$\sigma(x) \equiv x^{N\mathfrak{p}} \pmod{\mathfrak{P}}$ for all $x \in \mathcal{O}_L$, form a
conjugacy class $\mathrm{Frob}_{\mathfrak{p}}$ of $G$. Then the set

$$T = \{\mathfrak{p} \text{ unramified in } L : \mathrm{Frob}_{\mathfrak{p}} \subseteq C\}$$

has Dirichlet density $|C| / |G|$:

$$\sum_{\mathfrak{p} \in T} N\mathfrak{p}^{-s} = \frac{|C|}{|G|} \log \frac{1}{s - 1} + o\Bigl(\log \frac{1}{s - 1}\Bigr) \qquad (s \to 1^+,\ s \text{ real}).$$

Because the set of all nonzero prime ideals has Dirichlet density $1$ (Milne,
Proposition VI.4.4(a)), this is equivalent to
$\sum_{\mathfrak{p} \in T} N\mathfrak{p}^{-s} / \sum_{\mathfrak{p}} N\mathfrak{p}^{-s} \to |C| / |G|$
as $s \to 1^+$, the sum in the denominator running over all nonzero prime ideals of $\mathcal{O}_K$.

Milne's proof has three steps. Theorem VIII.7.2 is the equidistribution of prime ideals in ideal
classes: for a modulus $\mathfrak{m}$ and a congruence subgroup $H$, with
$I^{\mathfrak{m}} \supseteq H \supseteq i(K_{\mathfrak{m},1})$, the primes in each class of
$I^{\mathfrak{m}} / H$ have Dirichlet density $1 / (I^{\mathfrak{m}} : H)$. Milne combines
Theorem VI.4.8, whose proof gives the density $1 / (I^{\mathfrak{m}} : H)$ for the primes in $H$
provided $L(1, \chi) \neq 0$ for every nontrivial character $\chi$ of $I^{\mathfrak{m}} / H$, with
Theorem VIII.7.1, which supplies that non-vanishing.
Corollary VIII.7.3 is the abelian case: by the Reciprocity Law (Theorem V.3.5) the Artin map identifies
$\mathrm{Gal}(L/K)$ with such a quotient $I^{\mathfrak{m}} / H$ and sends an unramified prime to its
Frobenius element, so each element of $\mathrm{Gal}(L/K)$ is the Frobenius of a set of primes of
density $1 / [L : K]$. Theorem VIII.7.4 reduces the general case to the cyclic extension $L$ of the
fixed field $M$ of an element $\sigma$ of the class $C$, applying the abelian case to $L/M$ and
counting primes of $M$ of degree one over $K$.

The non-vanishing of $L(1, \chi)$ can be obtained in two ways. Milne derives Theorem VIII.7.1 from the
proof of the Second Inequality (Theorem VI.4.9 and Corollary VI.4.10) "once one has the Reciprocity
Law": that proof gives $L(1, \chi) \neq 0$ when some Galois extension has its norm group in the kernel
of $\chi$, and the Existence Theorem (Theorem V.3.6) provides such an extension for every $\chi$, as
he notes at the end of Chapter VI.
Alternatively, through the isomorphism between ray class groups and quotients of the idèle class group
(Milne, Proposition V.4.6), these characters are Hecke characters of finite order, and their
$L$-functions differ from those of
[the continuation page](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md)
by finitely many Euler factors, which do not vanish at $s = 1$; the analytic
[non-vanishing on the line Re s = 1](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-nonvanishing-on-re-one.md)
then gives $L(1, \chi) \neq 0$ directly, without the Existence Theorem. The edges below follow this
second route, with the Reciprocity Law for the abelian case.

## Depends on

- [Frobenius conjugacy class](../../../RingTheory/ramification/frobenius-elements/conjugacy-class-of-the-arithmetic-frobenius-at-a/arith-frob-conj-class.md)

## Proof depends on

- [Meromorphic continuation of Hecke L-functions](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md)
- [Non-vanishing of Hecke L-functions on the line Re s = 1](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-nonvanishing-on-re-one.md)
- [Global Artin reciprocity](global-artin-reciprocity.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VIII.7.4 (the statement, with Dirichlet
  density) and its proof; Theorems VIII.7.1 and VIII.7.2 and Corollary VIII.7.3; Section VI.4
  (definition of Dirichlet density, Proposition 4.4, Theorem 4.8, Theorem 4.9, Corollary 4.10 and the
  remark after it on the Existence Theorem); Theorem V.3.23 (the statement with $C$ a conjugacy class),
  Theorem V.3.5 (Reciprocity Law, ideal-theoretic form), Theorem V.3.6 (Existence Theorem) and
  Proposition V.4.6.
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>: Theorem 28.9 (Chebotarev density
  theorem) and its proof.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>,
  no licence) uses this result, as `GroundTheory.Global.hasDirichletDensity_chebotarevSet`.
