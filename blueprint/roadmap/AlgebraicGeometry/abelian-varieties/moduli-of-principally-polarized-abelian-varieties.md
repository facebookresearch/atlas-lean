# Moduli of principally polarized abelian varieties and their compactifications

This node is still to be broken down. It covers the moduli of polarized
[abelian schemes](abelian-scheme.md) with level structure and, in the principally polarized case,
the toroidal and minimal compactifications of the moduli space that Faltings and Chai construct from
the degenerations of polarized abelian varieties into semi-abelian schemes.

For integers $g \ge 1$, $d \ge 1$ and $n \ge 1$, Chai and Oort write $\mathcal{A}_{g,d,n}$ for the
moduli space of $g$-dimensional abelian varieties with a [polarization](polarization.md) of degree
$d^2$ and a symplectic level-$n$ structure, over schemes on which $n$ is invertible, and
$\mathcal{A}_g$ for the principally polarized case; over a field $K$ of characteristic prime to $n$,
$\mathcal{A}_{g,1,n} \otimes K$ is geometrically irreducible (Chai–Oort, (10.17), citing Faltings–Chai,
IV.5.10). A good expansion follows Faltings–Chai and has pages for:

- dual abelian schemes over a general base and polarizations of abelian schemes (Faltings–Chai,
  first chapter, pp. 1–30), extending the [dual abelian variety](dual-abelian-variety.md) of a field;
- the moduli schemes of polarized abelian schemes with level-$n$ structure, and their representability
  for level structures that rigidify the moduli problem;
- the degeneration data of a polarized semi-abelian scheme over a complete normal base whose generic
  fibre is abelian (Faltings–Chai, chapter "Degeneration of Polarized Abelian Varieties",
  pp. 31–52), and their inverse, [Mumford's construction](mumford-construction-of-degenerating-abelian-varieties.md)
  (chapter "Mumford's Construction", pp. 53–92);
- the toroidal compactifications of $\mathcal{A}_g$ and of its versions with level structure, attached
  to admissible polyhedral cone decompositions: smooth proper algebraic spaces or, for suitable
  decompositions, projective schemes, whose boundary is a divisor with normal crossings and over which
  the universal abelian scheme extends to a semi-abelian scheme (chapter "Toroidal Compactification of
  $A_g$", pp. 93–135);
- Siegel modular forms as sections of powers of the Hodge bundle, the Koecher principle, and the
  minimal compactification as the projective spectrum of the graded ring of modular forms (chapter
  "Modular Forms and the Minimal Compactification", pp. 136–193).

## Depends on

- [Abelian scheme](abelian-scheme.md)
- [Polarization](polarization.md)

## Sources

- G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Ergebnisse der Mathematik (3) 22,
  Springer, 1990: the chapters "Degeneration of Polarized Abelian Varieties" (pp. 31–52), "Mumford's
  Construction" (pp. 53–92), "Toroidal Compactification of A_g" (pp. 93–135) and "Modular Forms and
  the Minimal Compactification" (pp. 136–193), and IV.5.10 (irreducibility, as cited by Chai–Oort).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (10.11)
  (the moduli spaces $\mathcal{A}_g$, $\mathcal{A}_{g,d}$ and $\mathcal{A}_{g,d,n}$), (10.16) (3)
  (algebraization of polarized deformations) and (10.17) (irreducibility of
  $\mathcal{A}_{g,1,n} \otimes K$).
- D. Mumford, "An analytic construction of degenerating abelian varieties over complete rings",
  Compositio Math. 24 (1972), 239–272, <http://www.numdam.org/item?id=CM_1972__24_3_239_0>.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses toroidal compactifications of Siegel moduli spaces with odd
  level $n \ge 3$ over $\mathbb{Z}[\zeta_n, 1/n]$, with a
  semi-abelian extension of the universal family and an ample twist of a power of the Hodge bundle,
  as `GlobalTheory.Published.SiegelToroidalIntegral`, and a related statement for moduli spaces
  attached to unitary groups over CM fields (smooth models with simple normal crossing boundary), as
  `GlobalTheory.Published.ToroidalCompactification`.
