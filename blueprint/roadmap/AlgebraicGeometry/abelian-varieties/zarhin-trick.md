# Zarhin's trick

For every [abelian variety](abelian-scheme.md) $A$ over a field $k$, with
[dual abelian variety](dual-abelian-variety.md) $A^\vee$, the abelian variety
$(A \times A^\vee)^4$ has a [principal polarization](polarization.md).

Since $A$ is a direct factor of $(A \times A^\vee)^4$, every abelian variety is a direct factor of a
principally polarized one. Milne's proof starts from a polarization $\lambda$ of $A$ with
$\operatorname{Ker}(\lambda) \subset A_m$ for an integer $m$ prime to the characteristic of $k$. By
Lagrange's four-square theorem there are integers $a, b, c, d$ with
$a^2 + b^2 + c^2 + d^2 \equiv -1 \pmod{m^2}$, and the matrix

$$\alpha = \begin{pmatrix} a & -b & -c & -d \\ b & a & d & -c \\ c & -d & a & b \\ d & c & -b & a \end{pmatrix} \in M_4(\mathbb{Z}) \subset \operatorname{End}(A^4)$$

commutes with $\lambda^4 = \operatorname{diag}(\lambda, \lambda, \lambda, \lambda)$ and satisfies
$\alpha^\vee \circ \lambda^4 \circ \alpha = (a^2 + b^2 + c^2 + d^2)\,\lambda^4$. Milne's
Corollary I.13.11, a criterion from the theory of Weil pairings, then shows that
$A^4 \times (A^4)^\vee$ is principally polarized. Zarhin recalls the statement for abelian varieties
over an arbitrary field, with references to his papers of 1977 and 1985 and to Moret-Bailly's
*Pinceaux de variétés abéliennes*.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over a field
- [Dual abelian variety](dual-abelian-variety.md)
- [Polarization](polarization.md), for principal polarizations

## Proof depends on

- [Abelian varieties are projective](abelian-varieties-are-projective.md), for the existence of a
  polarization $\varphi_L$ with $L$ ample
- [Line bundles on abelian varieties](line-bundles-on-abelian-varieties.md), for Weil pairings and
  Milne's Corollary I.13.11

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Theorem 13.12 (Zarhin's trick) and its
  proof, Corollary 13.11, and the proof of Corollary 13.13 (direct factors).
- Yu. G. Zarhin, "Abelian varieties over fields of finite characteristic", Open Math. 12 (2014),
  659–674, arXiv:1301.5594 (version 4): §3, proof of Theorem 3.1 ("$(Y \times Y^t)^4$ admits a
  principal polarization over $K$", for an abelian variety $Y$ over a field $K$, with references to
  Zarhin, Math. Notes 21 (1977), 415–419; Zarhin, Invent. Math. 79 (1985), 309–321; and
  L. Moret-Bailly, *Pinceaux de variétés abéliennes*, Astérisque 129, 1985).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses a related statement for abelian schemes over valuation rings,
  that an abelian scheme with a relatively ample invertible sheaf is a retract of a principally
  polarized one, as `GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement`.
