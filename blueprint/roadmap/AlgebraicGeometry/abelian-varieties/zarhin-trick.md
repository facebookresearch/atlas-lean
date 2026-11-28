# Zarhin's trick

For every [abelian variety](abelian-scheme.md) $A$ over a field $k$, with
[dual abelian variety](dual-abelian-variety.md) $A^\vee$, the abelian variety
$A^4 \times (A^\vee)^4$ has a [principal polarization](polarization.md).

Since $A$ is a direct factor of $A^4 \times (A^\vee)^4$, every abelian variety is a direct factor of a
principally polarized one. Van der Geer and Moonen prove the theorem over an arbitrary field. Choose a
polarization $\lambda$ of $A$, which exists because $A$ is projective, and an integer $m \ge 1$ with
$\operatorname{Ker}(\lambda) \subset A[m]$. By [Lagrange's four-square
theorem](../../NumberTheory/quadratic-forms-sums-of-squares/sums-of-squares/lagrange-four-square-theorem.md)
there are integers $a, b, c, d$ with $a^2 + b^2 + c^2 + d^2 = m - 1$; the matrix

$$\alpha = \begin{pmatrix} a & -b & -c & -d \\ b & a & -d & c \\ c & d & a & -b \\ d & -c & b & a \end{pmatrix} \in M_4(\mathbb{Z}),$$

the matrix of left multiplication by the quaternion $a + bi + cj + dk$, satisfies
${}^t\alpha\, \alpha = (m - 1) \cdot \mathrm{id}_4$. Put $Y = A^4$, $\mu = \lambda^4$, and let $[\alpha]$ be
the endomorphism of $Y$ given by $\alpha$, so that $\mu \circ [\alpha] = [\alpha]_{A^\vee} \circ \mu$.
The isogeny $f \colon Y \times Y \to Y \times Y^\vee$, $(y_1, y_2) \mapsto (y_1 - [\alpha](y_2),
\mu(y_2))$, has kernel $\{([\alpha](y), y) : y \in \operatorname{Ker}(\mu)\}$, and by the descent
criterion for polarizations along isogenies the polarization $\mu \times \mu$ of $Y \times Y$ is
$f^\vee \circ \nu \circ f$ for a polarization $\nu$ of $Y \times Y^\vee$ if and only if
$1 + [{}^t\alpha\, \alpha] = m$ kills $\operatorname{Ker}(\mu) = \operatorname{Ker}(\lambda)^4$, which
holds; as $\deg f = \deg \mu$, the polarization $\nu$ is principal. Milne's proof of the same theorem
(his Theorem I.13.12) assumes that $m$ is prime to the characteristic of $k$, which an arbitrary
polarization need not allow (the kernel of $\varphi_L$ for $L = \mathcal{O}(p[0])$ on an elliptic curve
in characteristic $p$ is the $p$-torsion group scheme); the theory of finite group schemes removes that
restriction (Milne, Storrs article, Remark 16.13). Zarhin also gives a proof in arbitrary
characteristic, through the graph of an endomorphism and a maximal isotropic subgroup scheme.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over a field
- [Dual abelian variety](dual-abelian-variety.md)
- [Polarization](polarization.md), for principal polarizations

## Proof depends on

- [Abelian varieties are projective](abelian-varieties-are-projective.md), for the existence of a
  polarization $\varphi_L$ with $L$ ample
- [Line bundles on abelian varieties](line-bundles-on-abelian-varieties.md), for the descent criterion
  for polarizations along isogenies, the matrices $[\alpha]$ and their duals, and an integer $m$ with
  $\operatorname{Ker}(\lambda) \subset A[m]$
- [Lagrange's four-square theorem](../../NumberTheory/quadratic-forms-sums-of-squares/sums-of-squares/lagrange-four-square-theorem.md)

## Sources

- G. van der Geer and B. Moonen, *Abelian Varieties*, book draft, Chapter XI, "Polarizations and Weil
  pairings", <https://www.math.ru.nl/personal/bmoonen/BookAV/PolWp.pdf>: Theorem (11.29) (Zarhin's
  trick) with its proof, pp. 170–171, and Remarks (11.30).
- Yu. G. Zarhin, "Homomorphisms of abelian varieties over finite fields", in *Higher-Dimensional
  Geometry over Finite Fields*, IOS Press, 2008, 315–343; arXiv:0711.1615 (version 5),
  <https://arxiv.org/abs/0711.1615v5>: §7, "Quaternion trick", Lemma 7.1 and what follows.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Theorem 13.12 (Zarhin's trick) and its
  proof, Corollary 13.11, and the proof of Corollary 13.13 (direct factors).
- J. S. Milne, "Abelian varieties", in *Arithmetic Geometry* (Storrs, 1984), Springer, 1986,
  103–150; revised version of 2 January 2022, <https://www.jmilne.org/math/xnotes/AVs.pdf>:
  Remark 16.13.
- Yu. G. Zarhin, "Abelian varieties over fields of finite characteristic", Open Math. 12 (2014),
  659–674, arXiv:1301.5594 (version 4): §3, proof of Theorem 3.1 ("$(Y \times Y^t)^4$ admits a
  principal polarization over $K$", recalled with references to Zarhin, Math. Notes 21 (1977),
  415–419; Zarhin, Invent. Math. 79 (1985), 309–321; and L. Moret-Bailly, *Pinceaux de variétés
  abéliennes*, Astérisque 129, 1985).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the relative statement for abelian schemes over valuation rings, that
  an abelian scheme with a relatively ample invertible sheaf is a retract of a principally polarized
  one, as `GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement`; it is a related statement, the subject of
  the node on Zarhin's trick for abelian schemes.
