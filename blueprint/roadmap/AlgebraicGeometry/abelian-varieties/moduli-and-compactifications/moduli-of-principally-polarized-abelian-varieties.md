# Moduli of principally polarized abelian varieties and their compactifications

This node is still to be broken down. It covers the moduli of polarized
[abelian schemes](../abelian-scheme.md) with level structure and, in the principally polarized case,
the toroidal and minimal compactifications of the moduli spaces that Faltings and Chai construct from
the degenerations of polarized abelian varieties into semi-abelian schemes.

For $g \ge 1$, principally [polarized](../polarization.md) abelian schemes of relative dimension $g$ form
an algebraic stack $\mathcal{A}_g$ over $\mathbb{Z}$, with a coarse moduli space; the stack is not
represented by a scheme carrying a universal family: already for $g = 1$, an elliptic curve and a
nontrivial quadratic twist have the same $j$-invariant, and every principally polarized abelian
variety has the automorphism $-1$. For an integer $n \ge 3$ and a primitive $n$-th root of unity
$\zeta_n$, the principally polarized abelian schemes with a full symplectic level-$n$ structure whose
Weil pairing is given by $\zeta_n$ are classified by a scheme $\mathcal{A}_{g,1,n}$ over
$\mathbb{Z}[1/n, \zeta_n]$ carrying a universal family, and its geometric fibres are irreducible. Fixing $\zeta_n$ matters: over $\mathbb{C}$, allowing every primitive value of
the Weil pairing gives a union of open and closed pieces, one for each value. Chai and Oort, working in
characteristic $p$, write $\mathcal{A}_g$ for the moduli space of polarized abelian varieties,
$\mathcal{A}_{g,d}$ when the polarizations have degree $d^2$ and $\mathcal{A}_{g,d,n}$ with a symplectic
level-$n$ structure, $n$ prime to $p$; for $d > 1$ a level structure prime to the degree is needed for
a perfect pairing.

A good expansion follows Faltings–Chai and has pages for:

- the moduli stack $\mathcal{A}_g$, its coarse space, and the moduli schemes $\mathcal{A}_{g,1,n}$ for
  $n \ge 3$ with fixed $\zeta_n$, with their representability and the irreducibility of their
  geometric fibres (Chai–Oort, (10.17), citing Faltings–Chai, IV.5.10; Yu, introduction);
- the degeneration data of a polarized semi-abelian scheme over a complete normal base whose generic
  fibre is abelian (Faltings–Chai, chapter "Degeneration of Polarized Abelian Varieties",
  pp. 31–52), and their inverse, which generalizes [Mumford's
  construction](mumford-construction-of-degenerating-abelian-varieties.md) of the totally toric case
  (chapter "Mumford's Construction", pp. 53–92);
- the toroidal compactifications of $\mathcal{A}_{g,1,n}$, $n \ge 3$, attached to admissible polyhedral
  cone decompositions: proper algebraic spaces over which the universal abelian scheme extends to a
  semi-abelian scheme; smooth, with a boundary that is a divisor with normal crossings, when the cone
  decomposition is smooth; projective over the base when the decomposition is projective, with a
  boundary-supported effective Cartier divisor $D'$ such that $\mathcal{O}(-D')$ is relatively ample
  over the minimal compactification (chapter "Toroidal Compactification of $A_g$", pp. 93–135; Lan,
  Definition 2.2, Remark 2.3, Theorem 6.1 and Corollaries 6.6–6.7; Madapusi Pera, Theorem 2);
- Siegel modular forms as sections of powers of the Hodge bundle; the Koecher principle, which extends
  sections from the interior over the boundary for $g \ge 2$ but fails for $g = 1$, where a modular form
  must be required to be holomorphic at the cusps (the $j$-function has a pole there); and the minimal
  compactification as the projective spectrum of the graded ring of modular forms holomorphic at the
  boundary (chapter "Modular Forms and the Minimal Compactification", pp. 136–193; Lan, Theorem 8.7).

The stronger outputs that Alpöge's library uses, for specific levels, fans and bases, are the subject of
the nodes [Hodge bundle on toroidal compactifications of Siegel moduli
schemes](hodge-bundle-on-siegel-toroidal-compactifications.md) and [Toroidal compactifications of
unitary Shimura varieties](toroidal-compactifications-of-unitary-shimura-varieties.md).

## Depends on

- [Abelian scheme](../abelian-scheme.md)
- [Polarization](../polarization.md)

## Proof depends on

- [Mumford's construction of degenerating abelian varieties](mumford-construction-of-degenerating-abelian-varieties.md),
  for the totally toric case of the inverse of the degeneration data, which Faltings and Chai
  generalize

## Sources

- G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Ergebnisse der Mathematik (3) 22,
  Springer, 1990: the chapters "Degeneration of Polarized Abelian Varieties" (pp. 31–52), "Mumford's
  Construction" (pp. 53–92), "Toroidal Compactification of A_g" (pp. 93–135) and "Modular Forms and
  the Minimal Compactification" (pp. 136–193), and IV.5.10 (irreducibility, as cited by Chai–Oort).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (10.11)
  (the notations $\mathcal{A}_g$, $\mathcal{A}_{g,d}$ and $\mathcal{A}_{g,d,n}$ in characteristic $p$),
  (10.16) and (10.17) (irreducibility of $\mathcal{A}_{g,1,n} \otimes K$ for $n$ prime to the
  characteristic of $K$).
- C.-F. Yu, "Irreducibility and p-adic monodromies on the Siegel moduli spaces", arXiv:math/0612839
  (version 3): introduction, p. 1 (the moduli scheme $\mathcal{A}_{g,1,N}$ over
  $\mathbb{Z}_{(p)}[\zeta_N]$ for $N \ge 3$ prime to $p$ and a fixed $\zeta_N$, with irreducible geometric
  fibres).
- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>: §5.2.1
  (algebraic stacks of abelian varieties).
- K.-W. Lan, "Integral models of toroidal compactifications with projective cone decompositions",
  <https://www.kwlan.org/articles/cpt-ram-nbl.pdf>: Definition 2.2, Remark 2.3, Theorem 6.1,
  Corollaries 6.6 and 6.7, and Theorem 8.7 (Koecher's principle, with its hypotheses).
- K. Madapusi Pera, "Toroidal compactifications of integral models of Shimura varieties of Hodge
  type", arXiv:1211.1731: introduction, Theorem 2.
- D. Mumford, "An analytic construction of degenerating abelian varieties over complete rings",
  Compositio Math. 24 (1972), 239–272, <http://www.numdam.org/item?id=CM_1972__24_3_239_0>.
