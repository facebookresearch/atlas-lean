# Meromorphic continuation of Hecke L-functions

Let $K$ be a number field, $\mathbb{I}_K$ its idèle group and $|\cdot|$ the idèle norm. A unitary
Hecke character of $K$ is a continuous homomorphism $\chi \colon \mathbb{I}_K \to \mathbb{C}^\times$
with $|\chi(x)| = 1$ for all $x$ and $\chi(K^\times) = 1$, that is, a unitary character of the
[idèle class group](../../algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/topological-idele-class-group.md).
For a finite place $v$ let $\chi_v$ be the restriction of $\chi$ to $K_v^\times$, $\varpi_v$ a
uniformizer and $q_v$ the order of the residue field; $\chi$ is unramified at $v$ if $\chi_v$ is
trivial on the units $\mathcal{O}_v^\times$, and then $\chi_v(\varpi_v)$ does not depend on the
choice of $\varpi_v$. The Hecke $L$-function of $\chi$ is the Euler product

$$L(s, \chi) = \prod_{v \text{ finite},\ \chi \text{ unramified at } v} \bigl(1 - \chi_v(\varpi_v)\, q_v^{-s}\bigr)^{-1},$$

which converges absolutely to a holomorphic function without zeros on $\operatorname{Re} s > 1$. Then
$L(s, \chi)$ extends to a meromorphic function on $\mathbb{C}$:

1. if $\chi$ is not of the form $|\cdot|^{i\tau}$ with $\tau \in \mathbb{R}$, the extension is entire;
2. if $\chi = |\cdot|^{i\tau}$, then $L(s, \chi) = \zeta_K(s + i\tau)$, with $\zeta_K$ the Dedekind zeta
   function of $K$, and the extension is holomorphic except for a simple pole at $s = 1 - i\tau$.

The same continuation holds for the completed $L$-function
$\Lambda(s, \chi) = L_\infty(s, \chi) \, L(s, \chi)$, where $L_\infty(s, \chi)$ is the product over the
infinite places $v$ of the local factors of Tate's thesis, the functions
$\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ and $\Gamma_{\mathbb{C}}(s) = 2(2\pi)^{-s}\Gamma(s)$
evaluated at $s$ shifted by the parameters of $\chi_v$ (Poonen, §4.7). The function $\Lambda(s, \chi)$
is holomorphic except possibly at the points $s$ where $\chi |\cdot|^s$ is $|\cdot|^0$ or $|\cdot|^1$,
that is, at $s = -i\tau$ and $s = 1 - i\tau$ when $\chi = |\cdot|^{i\tau}$, and is entire otherwise
(Poonen, Theorem 5.22(b)). Since the archimedean factors are meromorphic without zeros (Poonen, §4.7),
$L = \Lambda / L_\infty$ is entire when $\Lambda$ is; and for $\chi = |\cdot|^{i\tau}$ the pole of
$\zeta_K$ at $1$ is simple and is its only pole (Kirschmer, Theorems 4.1.3 and 4.1.4).

Tate's proof writes $\Lambda$, up to entire nowhere-vanishing local factors, as a global zeta integral
$\int_{\mathbb{I}_K} f(x) \chi(x) |x|^s \, d^\times x$ of a Schwartz–Bruhat function $f$ on the adèles,
and continues it by splitting the integral at $|x| = 1$ and applying the Poisson summation formula for
$K \subset \mathbb{A}_K$ (Poonen, Theorems 5.16 and 5.7). Hecke had proved the continuation in the
language of ideals (Hecke 1920, §6).

## Depends on

- [Topological idele class group](../../algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/topological-idele-class-group.md)
- [Adelic norm](../../algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/adelic-norm.md)

## Sources

- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: Definition 5.11 (idèle-class characters), §4.7 (local
  $L$-factors), Definition 5.20 and Theorem 5.22 (Hecke $L$-functions), Theorem 5.16 (global zeta
  integrals) and Theorem 5.7 (Poisson summation).
- E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. 6 (1920), 11–51, end of §6: the Hauptsatz, that $\xi(s; \lambda)$
  is entire for every character other than the principal one.
- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>, Section 4.1:
  Theorem 4.1.3 (continuation of $\zeta_K$ to $\mathbb{C} \setminus \{1\}$, after Hecke) and
  Theorem 4.1.4 (simple pole at $1$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GroundTheory.Global.HeckeCharacter.exists_LFunction_continuation`
  (the first case) and `GroundTheory.Global.HeckeCharacter.exists_LFunction_continuation_of_forall`
  (the second).
