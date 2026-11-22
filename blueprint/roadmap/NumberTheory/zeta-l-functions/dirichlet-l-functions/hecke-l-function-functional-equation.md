# Functional equation of Hecke L-functions

Let $K$ be a number field, $\chi$ a unitary Hecke character of $K$ and
$\Lambda(s, \chi) = L_\infty(s, \chi) \, L(s, \chi)$ its completed $L$-function, continued to a
meromorphic function on $\mathbb{C}$ as on the
[continuation page](hecke-l-function-meromorphic-continuation.md); it is holomorphic except possibly at
$s = -i\tau$ and $s = 1 - i\tau$ when $\chi = |\cdot|^{i\tau}$ with $\tau$ real. Then

$$\Lambda(s, \chi) = \varepsilon(s, \chi) \, \Lambda(1 - s, \chi^{-1})$$

as meromorphic functions of $s$, where $\varepsilon(s, \chi) = \prod_v \varepsilon(\chi_v |\cdot|_v^s)$ is
the product of the local $\varepsilon$-factors of Tate's thesis, taken with the standard additive
character of $\mathbb{A}_K / K$ and self-dual measures; only finitely many of them differ from $1$, and
$\varepsilon(s, \chi) = a e^{bs}$ for constants $a \neq 0$ and $b$, so it is entire and has no zeros.
Here $\chi^{-1} = \overline{\chi}$. The identity holds as an identity of meromorphic functions on all of
$\mathbb{C}$, also when $\chi = |\cdot|^{i\tau}$. As an equality of finite values it holds at every
$s$, except, when $\chi = |\cdot|^{i\tau}$, at $s = -i\tau$ and $s = 1 - i\tau$, the possible poles of
both sides (Poonen, Definition 5.20, Theorem 5.22 and the formula after it).

The value $W(\chi) = \varepsilon(1/2, \chi)$ is the root number of $\chi$, the central value of its
$\varepsilon$-factor. Since $\varepsilon(s, \chi) = a e^{bs}$, the equation reads
$\Lambda(s, \chi) = W(\chi) \, e^{b(s - 1/2)} \Lambda(1 - s, \chi^{-1})$; the factor $e^{b(s - 1/2)}$ is
not constant unless $b = 0$, and the constant becomes $W(\chi)$ only after $\Lambda$ is normalized
symmetrically, by a factor $e^{-bs/2}$ (applying the equation twice shows that $\chi^{-1}$ has the
same $b$). Hecke completed his
$L$-functions differently, as
$\xi(s; \lambda) = \gamma(\lambda) \Gamma(s; \lambda) A^s \zeta(s; \lambda)$, with a product of Gamma
factors $\Gamma(s; \lambda)$ and a constant $A$, and wrote his functional equation for a primitive
character in the other direction:
$\xi(1 - s; \overline{\lambda}) = W_{\mathrm{H}}(\lambda) \, \xi(s; \lambda)$, with a constant
$W_{\mathrm{H}}(\lambda)$ of absolute value $1$ (Hecke 1920, equation (45)). The two constants belong to
different conventions: for one and the same completed function, writing the equation in the reverse
direction replaces its constant by the inverse.

In Tate's proof the functional equation comes from the global functional equation
$Z(f, \chi) = Z(\hat f, \chi^\vee)$ of the zeta integrals, with $\chi^\vee = \chi^{-1} |\cdot|$, which
is the Poisson summation formula on $\mathbb{A}_K$, and from the local functional equations that define
the local $\varepsilon$-factors (Poonen, Theorems 5.16(c) and 4.18(e) and the proof of Theorem 5.22).

## Depends on

- [Meromorphic continuation of Hecke L-functions](hecke-l-function-meromorphic-continuation.md)
- [Topological idele class group](../../algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/topological-idele-class-group.md)
- [Adelic norm](../../algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/adelic-norm.md)

## Sources

- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: Definition 5.20, Theorem 5.22 (a), (b) and (c), the
  formula $L(s, \chi) = \epsilon(s, \chi) L(1 - s, \chi^{-1})$ after its proof (Poonen's $L(s, \chi)$ is the
  completed function, with the archimedean factors), Remark 5.21, Theorem 4.18(e) (local
  $\epsilon$-factors of the form $a e^{bs}$) and Theorem 5.16.
- E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. 6 (1920), 11–51, end of §6: the Hauptsatz and equation (45).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, normalised with a constant root number, as
  `GroundTheory.Global.HeckeCharacter.completedLFunction_eq_rootNumber_mul`.
