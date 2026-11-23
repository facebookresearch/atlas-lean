# De Rham cohomology of abelian schemes

This node is still to be broken down. It covers the first de Rham cohomology of an
[abelian scheme](abelian-scheme.md) $A$ of relative dimension $g$ over a ring $R$ and its Hodge
filtration, in the form used by the deformation theory of abelian schemes and by the Hodge bundle on
moduli spaces. The targets are:

1. (Freeness.) $H^1_{\mathrm{dR}}(A/R)$ is a finite projective $R$-module of rank $2g$, and the cup
   product induces an isomorphism $\bigwedge^2 H^1_{\mathrm{dR}}(A/R) \cong H^2_{\mathrm{dR}}(A/R)$.
2. (Hodge filtration.) The Hodge filtration gives an exact sequence
   $0 \to \omega_{A/R} \to H^1_{\mathrm{dR}}(A/R) \to \operatorname{Lie}(A^t/R) \to 0$, with
   $\omega_{A/R} = e^* \Omega^1_{A/R}$ a direct summand, finite projective of rank $g$.
3. (Base change.) The formation of $H^1_{\mathrm{dR}}(A/R)$ and of its Hodge filtration commutes with
   every base change $R \to R'$.
4. (Rigidity.) For a nilpotent divided power thickening $R \to R_0$ and $A_0 = A \times_R R_0$, the
   crystalline nature of $H^1_{\mathrm{dR}}$ identifies $H^1_{\mathrm{dR}}(A/R)$ with the value on $R$
   of the crystal of $A_0$; in particular it depends only on $A_0$.
5. (Duality.) The pairing on $H^1_{\mathrm{dR}}(A/R)$ attached to a line bundle $L$ on $A$ vanishes on
   $\omega_{A/R} \times \omega_{A/R}$, and it is perfect when $\varphi_L$ is an isomorphism.

A good expansion has pages for: the Hodge to de Rham spectral sequence of an abelian scheme and its
degeneration, with the identification of $H^\bullet_{\mathrm{dR}}$ with the exterior algebra on
$H^1_{\mathrm{dR}}$ (van der Geer and Moonen prove the degeneration over fields, Corollary (7.29)); the
identification of $H^1_{\mathrm{dR}}(A/R)$ with the Lie algebra of the universal vector extension of
$A^t$ and its crystalline nature (Messing, Mazur and Messing); and the polarization pairing and the
duality of $H^1_{\mathrm{dR}}(A/R)$ with $H^1_{\mathrm{dR}}(A^t/R)$.

## Depends on

- [Abelian scheme](abelian-scheme.md)
- [Dual abelian scheme](dual-abelian-scheme.md), for $\operatorname{Lie}(A^t/R)$ and $\varphi_L$

## Sources

- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian Schemes*,
  Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and applications".
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1):
  Theorem 2.4 (iii) (the comparison with de Rham homology and the Hodge filtration).
- G. van der Geer and B. Moonen, *Abelian Varieties*, book draft, Chapter VII, "Duality",
  <https://www.math.ru.nl/personal/bmoonen/BookAV/DualAV2.pdf>: the Hodge–de Rham spectral sequence
  and Corollary (7.29), pp. 107–108.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states a related package of these properties, with its own
  definitions of the primitive submodule and of the polarization form, as
  `GlobalTheory.Published.AbelianDeRham` (the conjunction of `Free`, `Hodge`, `BaseChange`, `Rigid`
  and `Duality`); no published source stating this package as a whole has been identified.
