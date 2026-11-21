# Non-vanishing of Hecke L-functions on the line Re s = 1

Let $K$ be a number field and $\chi$ a unitary Hecke character of $K$ that is not of the form
$|\cdot|^{i\tau}$ with $\tau$ real, $|\cdot|$ the idèle norm. Let $G \colon \mathbb{C} \to \mathbb{C}$ be
an entire function with $G(s) = L(s, \chi)$ for $\operatorname{Re} s > 1$, where $L(s, \chi)$ is the
Euler product over the finite places at which $\chi$ is unramified. Then

$$G(s) \neq 0 \qquad \text{for every } s \in \mathbb{C} \text{ with } \operatorname{Re} s \ge 1.$$

The continuation is supplied as a hypothesis, but by uniqueness of analytic continuation $G$ is the
entire continuation of $L(s, \chi)$ given by the
[continuation page](hecke-l-function-meromorphic-continuation.md); so the statement says that the
continued Hecke $L$-function has no zero with $\operatorname{Re} s \ge 1$. On
$\operatorname{Re} s > 1$ this is the non-vanishing of an absolutely convergent Euler product; the
content is the line $\operatorname{Re} s = 1$. In particular $L(1, \chi) \neq 0$ for every nontrivial
Hecke character $\chi$ of finite order, the case that the proof of the
[Chebotarev density theorem](../../algebraic-number-theory/adeles-class-field-theory/chebotarev-density-theorem.md)
uses.

A standard proof is Mertens's argument for $\zeta$ (Sutherland, Lemma 16.4 and Corollary 16.5). Let
$S$ be the finite set of finite places at which $\chi$ is ramified, and $L^S$ the Euler products over
the finite places outside $S$. Since $3 + 4\cos\theta + \cos 2\theta = 2(1 + \cos\theta)^2 \ge 0$,
the logarithm of $|\zeta_K^S(\sigma)^3 \, L(\sigma + it, \chi)^4 \, L^S(\sigma + 2it, \chi^2)|$ is a sum of
nonnegative terms for $\sigma > 1$, so this product is at least $1$. If $L(1 + it, \chi) = 0$, then the
simple pole of $\zeta_K$ at $1$ and the holomorphy of $L(s, \chi^2)$ at $1 + 2it$ make the product tend
to $0$ as $\sigma \to 1^+$, a contradiction. By the continuation page, $L(s, \chi^2)$ fails to be
holomorphic at $1 + 2it$ only if $\chi^2 = |\cdot|^{-2it}$. Then $\eta = \chi |\cdot|^{it}$ is a
nontrivial character with $\eta^2 = 1$ and $L(1 + it, \chi) = L(1, \eta)$, which is nonzero because
$\eta$ has finite order; for characters of finite order, which correspond to characters of ray class
groups, Sutherland proves $L(1, \chi) \neq 0$ through the density of primes in ray classes, without
class field theory (Corollary 22.22). (This sketch is written out here; the sources below state the
theorem.)

## Proof depends on

- [Meromorphic continuation of Hecke L-functions](hecke-l-function-meromorphic-continuation.md)

## Sources

- H. Jacquet and J. A. Shalika, *A non-vanishing theorem for zeta functions of $GL_n$*, Invent. Math.
  38 (1976), 1–16, §1: Theorem (1.3) ($L(s, \pi) \neq 0$ for $\operatorname{Re}(s) = 1$, for $n \ge 2$)
  and the remark after it, that for $n = 1$ the theorem is true and classical, $\pi$ being then a
  character of $\mathbb{I}/F^\times$ and $L(s, \pi)$ a Hecke $L$-function times its Gamma factor.
- E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. 6 (1920), 11–51, §7: Landau's theory of the Dedekind zeta function
  carries over to $\zeta(s; \lambda)$, giving equation (46),
  $\sum_{N(\mathfrak{p}) < x} \lambda(\mathfrak{p}) = O(x e^{-c\sqrt{\log x}})$, for every class or
  Größencharakter $\lambda$ other than the principal one.
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 16,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes16.pdf>, Lemma 16.4 and Corollary 16.5 (the
  argument for $\zeta$); Lecture 22, <https://math.mit.edu/classes/18.785/2021fa/LectureNotes22.pdf>,
  Proposition 22.19 and Corollary 22.22 (characters of ray class groups).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>,
  no licence) uses this result, in this form with the continuation supplied, as
  `GroundTheory.Global.HeckeCharacter.continuation_ne_zero_of_one_le_re`.
