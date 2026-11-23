# Zero-free half-planes from one-sided bounds for weighted Chebyshev sums on windows

For a Dirichlet character $\chi$ and a real number $y \ge 1$ let

$$\psi^\sharp(y, \chi) = \sum_{1 \le n \le y} \Lambda(n)\, \chi(n) \Bigl(\frac{y}{n} - 1\Bigr),$$

where $\Lambda$ is the von Mangoldt function, and put

$$G_\chi(y) = \psi^\sharp(y, \chi) - y \log y + (1 + \gamma)\, y$$

if $\chi$ is the trivial character modulo $1$, with $\gamma$ Euler's constant, and

$$G_\chi(y) = \psi^\sharp(y, \chi) + y\, \frac{L'(1, \chi)}{L(1, \chi)}$$

if $\chi$ is nonprincipal, that is, not the trivial character of its modulus.

Let $(\chi_i)_{i \in I}$ be a finite family of Dirichlet characters, each of which is either the
trivial character modulo $1$ or a nonprincipal character, let $a_i > 0$ for $i \in I$, and let
$G(y) = \sum_{i \in I} a_i \operatorname{Re} G_{\chi_i}(y)$. Let $0 < \theta < 1$, $\delta > 0$ and
$C \in \mathbb{R}$, and suppose that for every $Y_0 \ge 1$ there is $Y \ge Y_0$ with

$$G(y) \le C\, y^\theta \qquad \text{for all } y \in [Y, Y^{1 + \delta}].$$

Then $L(s, \chi_i) \ne 0$ for every $i \in I$ and every complex number $s$ with
$\operatorname{Re} s > \theta$; for the trivial character modulo $1$, whose $L$-function is the Riemann
zeta function, the pole $s = 1$ is excluded.

The bound is required only on the windows $[Y, Y^{1+\delta}]$, at arbitrarily large $Y$, not for all
large $y$. The correction terms make the Laplace transform
$\Phi(s) = \int_0^\infty G(e^u)\, e^{-su}\, du$, which converges for $\operatorname{Re} s > 2$, holomorphic
at $s = 1$. On $\operatorname{Re} s > 0$ it continues meromorphically, with simple poles at the zeros of
the $L(s, \chi_i)$ and of the $L(\bar s, \chi_i)$, whose residues are positive at real points. The
proof does not use Landau's theorem on
[Dirichlet integrals with non-negative integrands](analytic-continuation-of-dirichlet-series/landau-theorem-dirichlet-integrals.md),
whose hypothesis is a sign condition for all large arguments; it runs Landau's argument on the
windows instead. A zero with real part greater than $\theta$ would make the Taylor coefficients of
$\Phi$ at a real point $\sigma > 2$ larger than the window bounds allow. Zeros with
$\operatorname{Re} s \ge 1$ are excluded by the non-vanishing of $L(s, \chi)$ there.

## Proof depends on

- [Meromorphic continuation of Hecke L-functions](hecke-l-function-meromorphic-continuation.md), for its case of the finite-order Hecke characters of $\mathbb{Q}$: the $L$-functions of nonprincipal Dirichlet characters, which differ from those of their primitive characters by finitely many Euler factors, are entire, and the Riemann zeta function has a simple pole at $s = 1$ and no other pole
- [Non-vanishing of Hecke L-functions on the line Re s = 1](hecke-l-function-nonvanishing-on-re-one.md), for the same case: $L(s, \chi) \ne 0$ for $\operatorname{Re} s \ge 1$ when $\chi$ is a nonprincipal Dirichlet character, since the finitely many Euler factors that separate $\chi$ from its primitive character do not vanish there

## Sources

- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>); the Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited below by paths in it. The statement of this page is `Deduction.zeroFree_of_rpow_window` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean`, lines 11–14), for the families `Deduction.CharFamily` with the functions `ramp` ($\psi^\sharp$), `Gchi` ($G_\chi$), `Gm` ($G$) and the conclusion `ZeroFree` of `src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean`, lines 10–40. It is proved there through `Deduction.lemmaL` (`LandauTheorems/lemmaL.lean`, lines 13–22), with the Laplace transform and its poles in `Deduction.poleData` (`LandauTheorems/poleData.lean`, line 248) and the windowed argument in `Deduction.landau_window` (`LandauTheorems/landauWindow.lean`, line 83). The two inputs are consumed as Mathlib theorems: the holomorphy of $L(s, \chi)$ for nonprincipal $\chi$ (`DirichletCharacter.differentiable_LFunction`) at `poleData.lean`, line 231, and the simple pole of $\zeta$ at $s = 1$ (`differentiableAt_riemannZeta`, `riemannZeta_residue_one`) at lines 165–167; the non-vanishing on $\operatorname{Re} s \ge 1$ for nonprincipal $\chi$ (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`), with Mathlib's `riemannZeta_ne_zero_of_one_le_re` for the Riemann zeta function, in `Deduction.charFamily_LFunction_ne_zero_of_one_le_re` (`LandauTheorems/CharFamilyLFunctionNeZeroOfOneLeRe.lean`, lines 9–20), applied at `lemmaL.lean`, line 19, and at `poleData.lean`, lines 216, 232, 342–343 and 375–376. The library's other Landau-type criterion, `Formalism.HC.Landau.zero_free_of_Chebyshev_growth` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean`, line 538), which assumes the bound for all large $y$, is used there only through `Formalism.HC.level_of_tiedAll` and `Formalism.HC.zeroFreeOn_of_tiedAll` (`TotientGaloisClasses/TopWin.lean`, lines 117–134), on which the main theorems do not depend.
