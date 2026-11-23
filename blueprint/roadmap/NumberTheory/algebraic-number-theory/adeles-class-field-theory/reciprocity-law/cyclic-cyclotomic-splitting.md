# Classes in H² of a number field split over cyclic cyclotomic extensions

Let $K$ be a number field with algebraic closure $\overline{K}$, and call a finite extension $L/K$ cyclic
cyclotomic if $L/K$ is cyclic and $L \subseteq K(\zeta)$ for some root of unity $\zeta$. For every class
$\beta \in H^2(\mathrm{Gal}(\overline{K}/K), \overline{K}^\times)$ there is a cyclic cyclotomic extension
$L/K$ such that the restriction of $\beta$ to $H^2(\mathrm{Gal}(\overline{K}/L), \overline{K}^\times)$ is
zero; equivalently, $\beta$ is the inflation of a class in $H^2(\mathrm{Gal}(L/K), L^\times)$.

In terms of Brauer groups: every central simple algebra over $K$ splits over a cyclic cyclotomic extension
of $K$.

Milne's proof. By the [Hasse principle](hasse-principle-for-h2.md), $\beta$ is determined by its local
components $\beta_v$, hence by their invariants $\mathrm{inv}_v(\beta_v) \in \mathbb{Q}/\mathbb{Z}$, which
vanish for almost all $v$; and for a finite extension $L/K$ and a place $w \mid v$ of $L$, the invariant of
the restriction of $\beta$ at $w$ is $[L_w : K_v] \, \mathrm{inv}_v(\beta_v)$. So it suffices that the local
degrees $[L_w : K_v]$ be divisible by an integer $m$ with $m \, \mathrm{inv}_v(\beta_v) = 0$ for all $v$, at
the finitely many places where $\beta_v \ne 0$. Such an extension exists (Lemma VII.7.3): given a finite set
$S$ of finite places of $K$ and $m > 0$, there is a totally complex cyclic cyclotomic extension $L/K$ with
$m \mid [L_w : K_v]$ for all $v \in S$. Milne reduces to $K = \mathbb{Q}$ and composes, over several primes
$\ell$, cyclic subfields of the fields $\mathbb{Q}(\zeta_{\ell^r})$ of $\ell$-power degree, whose local
degrees at every prime tend to infinity with $r$. A totally complex $L$ kills the components at the real
places, whose invariants lie in $\tfrac12\mathbb{Z}/\mathbb{Z}$. (The subfields Milne names are real; for the
prime $2$ one can use instead the fixed field in $\mathbb{Q}(\zeta_{2^r})$, $r \ge 3$, of the element
$-(1 + 2^{r-1})$ of order $2$ of $(\mathbb{Z}/2^r\mathbb{Z})^\times$, which is imaginary and cyclic of degree
$2^{r-2}$, so that the composite is totally complex. This remark is not Milne's text.) The equivalence of
the two formulations is the inflation–restriction sequence in degree $2$, since
$H^1(\mathrm{Gal}(\overline{K}/L), \overline{K}^\times) = 0$.

## Proof depends on

- [Hasse principle for H² of the multiplicative group of a number field](hasse-principle-for-h2.md), for $\overline{K}/K$
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps and their behaviour under restriction (its item 2)
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for the inflation–restriction sequence (its item 2), for the equivalence of the two formulations

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Proposition VII.7.2 (the statement) and its proof,
  Lemma VII.7.3 and its proof, the remark after it (central simple algebras), and the note in the proof of
  Lemma VII.8.6 (the inflation–restriction sequence in degree $2$).
