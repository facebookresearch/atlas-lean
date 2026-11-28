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
nontrivial character with $\eta^2 = 1$ and $L(1 + it, \chi) = L(1, \eta)$, and $L(1, \eta) \neq 0$
follows from [Landau's theorem](analytic-continuation-of-dirichlet-series/landau-theorem-dirichlet-series.md): a Dirichlet series $\sum_{n \ge 1} c_n n^{-s}$ with $c_n \ge 0$ and real
abscissa of absolute convergence $\sigma_0$ does not extend to a holomorphic function on any
neighbourhood of $\sigma_0$ (Kedlaya, Theorem 2.4). Suppose $L(1, \eta) = 0$. By the continuation page,
$\zeta_K$ is holomorphic except for a simple pole at $1$, and $L(s, \eta)$ is entire because $\eta$ is
nontrivial of finite order; so $F(s) = \zeta_K(s) L(s, \eta)$ extends to an entire function. For
$\operatorname{Re} s > 1$, $F(s) = \sum_{\mathfrak{a}} a(\mathfrak{a}) N\mathfrak{a}^{-s}$ over the
nonzero ideals $\mathfrak{a}$ of $\mathcal{O}_K$, with $a$ multiplicative and determined by the Euler
factors (at a prime where $\eta$ is unramified, $\eta(\mathfrak{p}) = \pm 1$ since $\eta^2 = 1$): with
$x = N\mathfrak{p}^{-s}$, a prime $\mathfrak{p}$ with $\eta(\mathfrak{p}) = 1$ contributes
$(1 - x)^{-2} = \sum_{k \ge 0} (k + 1) x^k$, one with $\eta(\mathfrak{p}) = -1$ contributes
$(1 - x)^{-1} (1 + x)^{-1} = \sum_{k \ge 0} x^{2k}$, and one at which $\eta$ is ramified, whose factor
is absent from $L(s, \eta)$, contributes $(1 - x)^{-1} = \sum_{k \ge 0} x^k$. Hence
$a(\mathfrak{a}) \ge 0$ for every $\mathfrak{a}$, and $a(\mathfrak{b}^2) \ge 1$ for every $\mathfrak{b}$,
since all exponents in $\mathfrak{b}^2$ are even. Grouping ideals by norm writes $F$ as a Dirichlet
series with nonnegative coefficients, absolutely convergent for $\operatorname{Re} s > 1$. At $s = 1/2$
its terms indexed by the squares $\mathfrak{b}^2$ alone add up to
$\sum_{\mathfrak{b}} a(\mathfrak{b}^2) N\mathfrak{b}^{-1} \ge \sum_{\mathfrak{b}} N\mathfrak{b}^{-1}$, which
diverges because $\zeta_K(\sigma) = \sum_{\mathfrak{b}} N\mathfrak{b}^{-\sigma}$ tends to infinity as
$\sigma \to 1^+$; so the abscissa of absolute convergence lies in $[1/2, 1]$. Landau's theorem then
gives a singularity of $F$ there, contradicting that $F$ is entire. (This sketch is written out here; the sources below state the theorem.)

## Proof depends on

- [Meromorphic continuation of Hecke L-functions](hecke-l-function-meromorphic-continuation.md)
- [Landau's theorem on Dirichlet series with non-negative coefficients](analytic-continuation-of-dirichlet-series/landau-theorem-dirichlet-series.md)

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
  argument for $\zeta$).
- K. S. Kedlaya, *Notes on analytic number theory*, online notes, Chapter 2, Section 2.1,
  <https://kskedlaya.org/ant/part-1-3.html>: Theorem 2.4 (Landau) and its proof, with Lemma 2.2 and
  Definition 2.3 (abscissa of absolute convergence).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, in this form with the continuation supplied, as
  `GroundTheory.Global.HeckeCharacter.continuation_ne_zero_of_one_le_re`.
