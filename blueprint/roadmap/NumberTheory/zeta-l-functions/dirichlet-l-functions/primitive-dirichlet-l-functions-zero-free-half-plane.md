# Primitive Dirichlet L-functions have no zero of real part greater than 1/2

For every primitive Dirichlet character $\chi$ and every complex number $s$ with
$\operatorname{Re} s > 1/2$, $L(s, \chi) \ne 0$; for the trivial character modulo $1$, whose
L-function is the Riemann zeta function, the pole $s = 1$ is excluded.

The proof treats one primitive character $\psi$ at a time, together with the family $K_\psi$ of the
primitive characters that induce the powers of $\psi$. It applies the
[criterion on windows](zeros-of-dirichlet-l-functions/zero-free-half-planes-from-chebyshev-bounds-on-windows.md) to $K_\psi$, with
weight $1$ for the trivial character modulo $1$ and weight $1/(3o + 1)$ for the other characters,
where $o$ is the order of $\psi$. The hypothesis of the criterion, for every exponent
$\theta \in (1/2, 1)$ and on windows $[Y, Y^{3/2}]$, is the
[window bound for these weighted Chebyshev sums](../../distribution-of-primes/primes-in-progressions/chebyshev-window-bounds-for-cyclic-character-families.md).
That bound comes from Green's description of the cuspidal characters of
$\mathrm{GL}_n(\mathbb{F}_p)$, a window bound for Tate–Shafarevich groups of Tate twists over subfields
of cyclotomic fields, and the definite-side hypotheses, through intermediate statements about
families of auxiliary number fields. The criterion then gives
$L(s, \chi) \ne 0$ for $\chi \in K_\psi$ and $\operatorname{Re} s > \theta$, for every
$\theta > 1/2$, and in particular for $\chi = \psi$.

## Depends on

- [Dirichlet character of a given modulus](conductors-and-primitive-dirichlet-characters/is-dirichlet-character-modulus.md), for Dirichlet characters, of a positive modulus
- [Primitive characters at divisor levels](conductors-and-primitive-dirichlet-characters/primitive-inducer.md), for primitive characters, those whose conductor is their level: the case $d = m$ of a primitive inducer
- [Meromorphic continuation of Hecke L-functions](hecke-l-function-meromorphic-continuation.md), for the continued $L$-functions of the primitive characters other than the trivial character modulo $1$, on $\operatorname{Re} s > 1/2$, and, in its case $K = \mathbb{Q}$, $\chi = 1$, $\tau = 0$, for $\zeta$, the $L$-function of the trivial character modulo $1$, holomorphic on $\mathbb{C}$ except for a simple pole at $s = 1$

## Proof depends on

- [Zero-free half-planes from one-sided bounds for weighted Chebyshev sums on windows](zeros-of-dirichlet-l-functions/zero-free-half-planes-from-chebyshev-bounds-on-windows.md), for the step from the window bounds to the zero-free half-plane, applied to the families $K_\psi$
- [Window bounds for weighted Chebyshev sums of cyclic families of characters](../../distribution-of-primes/primes-in-progressions/chebyshev-window-bounds-for-cyclic-character-families.md), for the window bounds, which it derives from Green's description, the window bound for Tate–Shafarevich groups and the definite-side hypotheses

## Sources

- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>) whose five main theorems are two forms of the Riemann hypothesis (`riemannHypothesis`, `riemannZeta_eq_zero_re`) and three forms of the generalized Riemann hypothesis for Dirichlet L-functions (`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`). The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); A. Sutherland's independent checks cover the five main theorems (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited below by paths in it. The statement of this page is not among those five theorems: in the library it is the internal proposition `Formalism.HC.ZeroFreeAll`, over the primitive characters `Formalism.HC.PChar` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean`, lines 11–18, and `.../TotientGaloisClasses/PrimePairSizeCondition.lean`, lines 7–11); it has no exception at $s = 1$ because Mathlib gives $\zeta(1)$ a finite non-zero value. It is proved as `UpperTheory.Top.zero_free_all_of_green_v_win` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean`, lines 12–15) through `Formalism.HC.zeroFreeOn_of_tiedWin_cyc` and `Formalism.HC.level_of_tiedWin` (`.../TotientGaloisClasses/TopWin.lean`, lines 68–93), which apply the criterion through `UpperTheory.Comparison₂.formB` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean`, lines 8–19). The criterion is consumed at line 13 there, with $\delta = 1/2$ and $C = 1$, for the family that `UpperTheory.Comparison₂.level_family` attaches to $K_\psi$ (`src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelFamily.lean`, lines 41–52); the window bound is consumed at `TopWin.lean`, lines 76–81, where `level_of_tiedWin` obtains it from `UpperTheory.Comparison₂.level_gm_le_on_family_scales` and from the families that `UpperTheory.Top.zeroFreeAll_of_topG` supplies (`src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean`, lines 26–34). The main theorem `LFunction_ne_zero_of_half_lt_re` follows through `UpperTheory.Top.imprimitive` (`src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean`, lines 5–35), within `UpperTheory.Top.every_character_of_green_v_win` (`TopPlug.lean`, lines 16–18), `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean`, lines 69–73) and `UpperTheory.FinalTheorems.everyCharacter` (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`, lines 7–11).
