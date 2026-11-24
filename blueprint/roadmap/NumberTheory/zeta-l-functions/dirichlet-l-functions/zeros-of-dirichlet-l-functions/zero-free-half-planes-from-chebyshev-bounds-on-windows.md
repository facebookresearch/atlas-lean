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
large $y$. The Laplace transform $\Phi(s) = \int_0^\infty G(e^u)\, e^{-su}\, du$ converges for
$\operatorname{Re} s > 2$, where it is computed from the identity

$$-\frac{L'(s, \chi)}{L(s, \chi)} = \sum_{n \ge 1} \chi(n) \Lambda(n)\, n^{-s} \qquad (\operatorname{Re} s > 1):$$

$\Phi(s) = \sum_{i \in I} a_i \bigl(F_{\chi_i}(s) + \overline{F_{\chi_i}(\bar s)}\bigr)/2$, where
$F_\chi(s) = \int_1^\infty G_\chi(y)\, y^{-s-1}\, dy$ is
$-\bigl(\frac{L'}{L}(s, \chi) - s\, \frac{L'}{L}(1, \chi)\bigr)/(s(s - 1))$ for nonprincipal $\chi$ and
$-\frac{\zeta'}{\zeta}(s)/(s(s - 1)) - 1/(s - 1)^2 + (1 + \gamma)/(s - 1)$ for the trivial character
modulo $1$. The correction terms make $\Phi$ holomorphic at $s = 1$: for the trivial character this
uses the constant term $\gamma$ of the Laurent expansion $\zeta(s) = 1/(s - 1) + \gamma + O(s - 1)$, and
for the nonprincipal characters the values $L(1, \chi) \ne 0$. On $\operatorname{Re} s > 0$ it continues
meromorphically, with simple poles at the zeros of the $L(s, \chi_i)$ and of the $L(\bar s, \chi_i)$,
whose residues are positive at real points.

The proof runs Landau's argument on the windows instead of applying Landau's theorem on
[Dirichlet integrals with non-negative integrands](../analytic-continuation-of-dirichlet-series/landau-theorem-dirichlet-integrals.md),
whose hypothesis is a sign condition for all large arguments. Let
$a_k(z) = (-1)^k \Phi^{(k)}(z)/k!$, which for $\operatorname{Re} z > 2$ is
$\frac{1}{k!} \int_0^\infty G(e^u)\, u^k e^{-zu}\, du$. For a suitable $\sigma > 2$, every $\eta > 0$,
arbitrarily large windows $[Y, Y^{1+\delta}]$ and some $k \ge \log Y$, the bound on the window, with
$|G| \le 2|C| y^\theta - G$ there and the growth $G(y) = O(y^2)$ outside it, gives

$$|a_k(\sigma + i\gamma)| + \operatorname{Re} a_k(\sigma) \le C' Y^\eta (\sigma - \theta)^{-k} \qquad \text{for every real } \gamma,$$

a bound on a combination of the coefficients at two centres. Suppose that $\Phi$ has a pole of real
part greater than $\theta$, and let $d \le \sigma - \theta$ be the distance from $\sigma$ to the nearest
pole, or $d = \sigma - \theta$ if no pole lies within that distance. If every pole $\rho$ has
$\sigma - \operatorname{Re} \rho \ge d$, then $d < \sigma - \theta$ and the nearest pole is the real point
$\beta = \sigma - d > \theta$, alone in a slightly larger disc about $\sigma$; its residue $c$ is positive, so
$\operatorname{Re} a_k(\sigma) \ge c\, (\sigma - \beta)^{-k-1} - O(e^{-k})$ for some $e$ with
$\sigma - \beta < e \le \sigma - \theta$, which contradicts the bound. Otherwise some pole has
$\sigma - \operatorname{Re} \rho < d$, while the disc of radius $d$ about $\sigma$ contains no pole;
then for a suitable $\gamma$ a pole $\rho$ is the only pole near the vertically shifted centre
$\sigma + i\gamma$, at distance $d' = |\sigma + i\gamma - \rho| < d$, and
$|a_k(\sigma + i\gamma)| \ge |c|\, d'^{-k-1} - O(e^{-k})$ with $d' < e \le \sigma - \theta$, while Cauchy's
estimate on the pole-free disc bounds $|a_k(\sigma)|$ by $O(e^{-k})$, again contradicting the bound.
In both cases the contradiction takes $\eta > 0$ small enough in terms of the distance $d_0$ to the
pole and the radius $e > d_0$ ($\eta = \tfrac12 \log(e/d_0)$ suffices) and uses $k \ge \log Y$: then
$|c|\, d_0^{-k-1}$ exceeds $O(e^{-k}) + C' Y^\eta (\sigma - \theta)^{-k}$ for all large $Y$. So every
zero of the $L(s, \chi_i)$ with $0 < \operatorname{Re} s < 1$ has real part at most $\theta$; zeros with
$\operatorname{Re} s \ge 1$ are excluded by the non-vanishing of the $L$-functions there, which for
the trivial character modulo $1$ is the non-vanishing of $\zeta(s)$, $s \ne 1$, on
$\operatorname{Re} s \ge 1$.

## Depends on

- [Dirichlet character of a given modulus](../conductors-and-primitive-dirichlet-characters/is-dirichlet-character-modulus.md), for Dirichlet characters, of a positive modulus
- [Meromorphic continuation of Hecke L-functions](../hecke-l-function-meromorphic-continuation.md), for the continued $L$-functions of the nonprincipal characters, whose values $L(1, \chi)$ and $L'(1, \chi)$ and whose zeros the statement involves, and, in its case $K = \mathbb{Q}$, $\chi = 1$, $\tau = 0$, for $\zeta$, the $L$-function of the trivial character modulo $1$, holomorphic on $\mathbb{C}$ except for a simple pole at $s = 1$
- [Stieltjes constants exist, and the zeroth is Euler's constant](../../riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullipol.md), for Euler's constant $\gamma$, the limit of $\sum_{j \le m} 1/j - \log m$ (the case $k = 0$)
- [Von Mangoldt function](../../../arithmetic-functions/multiplicative-functions/von-mangoldt-function.md), for the function $\Lambda$ in the weighted Chebyshev functions $\psi^\sharp$

## Proof depends on

- [Dirichlet series of the twisted von Mangoldt function as a logarithmic derivative](../dirichlet-series-of-arithmetic-functions/l-series-twist-von-mangoldt.md), for the identity $-L'(s, \chi)/L(s, \chi) = \sum_{n \ge 1} \chi(n) \Lambda(n)\, n^{-s}$ on $\operatorname{Re} s > 1$, by which the Laplace transform is computed: for the nonprincipal characters, and, in its case of the modulus $1$, where it reads $-\zeta'(s)/\zeta(s) = \sum_{n \ge 1} \Lambda(n)\, n^{-s}$, for the trivial character
- [Meromorphic continuation of Hecke L-functions](../hecke-l-function-meromorphic-continuation.md), for its case of the finite-order Hecke characters of $\mathbb{Q}$: the $L$-functions of nonprincipal Dirichlet characters, which differ from those of their primitive characters by finitely many Euler factors, are entire, and, in its case $K = \mathbb{Q}$, $\chi = 1$, $\tau = 0$, the Riemann zeta function is holomorphic on $\mathbb{C}$ except for a simple pole at $s = 1$, which gives the meromorphic continuation of $\Phi$ for the trivial character
- [Non-vanishing of Hecke L-functions on the line Re s = 1](../hecke-l-function-nonvanishing-on-re-one.md), for the same case, for nonprincipal characters only: $L(s, \chi) \ne 0$ for $\operatorname{Re} s \ge 1$, in particular $L(1, \chi) \ne 0$, when $\chi$ is a nonprincipal Dirichlet character, since the finitely many Euler factors that separate $\chi$ from its primitive character do not vanish there
- [Nonvanishing of the Riemann zeta function times $s - 1$ on $\operatorname{Re} s \ge 1$](../../../distribution-of-primes/prime-number-theorem/prime-number-theorem/riemann-zeta-ne-zero-of-one-le-re.md), for the trivial character modulo $1$, which the page on Hecke $L$-functions excludes as the norm power $|\cdot|^0$
- [Laurent expansion of $\zeta$ at $s = 1$](../../riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullirec.md), for its constant term: $\zeta(s) - 1/(s - 1)$ tends to the zeroth Stieltjes constant $c_0$ as $s \to 1$
- [Stieltjes constants exist, and the zeroth is Euler's constant](../../riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullipol.md), for $c_0 = \gamma$, so that the constant term of $\zeta$ at $s = 1$ is Euler's constant
- [A function holomorphic on a closed disc is the sum of its Cauchy power series](../../../../Analysis/complex-analysis/cauchy-theory/cauchy-integral-theorem-and-formula/differentiable-on-has-f-power-series-on-ball.md), for the expansions about the centres $\sigma$ and $\sigma + i\gamma$ of $\Phi$ and of its parts without the pole, whose coefficients $a_k(z) = (-1)^k \Phi^{(k)}(z)/k!$ are, up to sign, those of the Cauchy power series
- [Cauchy's estimate for the coefficients of the Cauchy power series](../../../../Analysis/complex-analysis/cauchy-theory/contour-integrals-and-antiderivatives/norm-cauchy-power-series-le.md), for the bound $O(e^{-k})$ on the coefficients of the parts without the pole, from circles of radius $e$ on which they are holomorphic

## Sources

- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>); the Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited below by paths in it. The statement of this page is `Deduction.zeroFree_of_rpow_window` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean`, lines 11–14), for the families `Deduction.CharFamily` with the functions `ramp` ($\psi^\sharp$), `Gchi` ($G_\chi$), `Gm` ($G$) and the conclusion `ZeroFree` of `src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean`, lines 10–40. It is proved there through `Deduction.lemmaL` (`LandauTheorems/lemmaL.lean`, lines 13–22), with the Laplace transform and its poles in `Deduction.poleData` (`LandauTheorems/poleData.lean`, line 248). The inputs are consumed as Mathlib theorems: the identity of the logarithmic derivative, `DirichletCharacter.LSeries_twist_vonMangoldt_eq`, for the nonprincipal characters at `LandauTheorems/mellinGchiOfNeOne.lean`, lines 126–128, and its form for $\zeta$, `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (the case of the modulus $1$), for the trivial character at `LandauTheorems/mellinGchiModOne.lean`, lines 191–193; the holomorphy of $L(s, \chi)$ for nonprincipal $\chi$ (`DirichletCharacter.differentiable_LFunction`) and $L(1, \chi) \ne 0$ (`DirichletCharacter.LFunction_apply_one_ne_zero`) at `poleData.lean`, lines 231–232; the simple pole of $\zeta$ at $s = 1$ (`differentiableAt_riemannZeta`, `riemannZeta_residue_one`) at lines 165–167, and its Laurent constant term $\gamma$ (`tendsto_riemannZeta_sub_one_div`, giving `deriv g 1 = γ` for $g(s) = (s - 1)\zeta(s)$) at lines 168–176, used at line 218, so that $s = 1$ is a removable singularity of the corrected transform $\Phi$, not one of its poles (lines 149–176 and 204–218); the non-vanishing on $\operatorname{Re} s \ge 1$ in `Deduction.charFamily_LFunction_ne_zero_of_one_le_re` (`LandauTheorems/CharFamilyLFunctionNeZeroOfOneLeRe.lean`, lines 9–20), which splits into the trivial character modulo $1$ (`riemannZeta_ne_zero_of_one_le_re`, lines 13–19) and the nonprincipal characters (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`, line 20), applied at `lemmaL.lean`, line 19, and at `poleData.lean`, lines 342–343 and 375–376, with `riemannZeta_ne_zero_of_one_le_re` also at line 216. The windowed argument is `Deduction.landau_window` (`LandauTheorems/landauWindow.lean`, lines 83–165): the combined bound is `landau_window_key` (lines 40–73, from `landau_window_ineq` and `landau_tails`), which obtains the particular $k$ at lines 46 and 53–56, the case split is `landau_dichotomy` (`LandauTheorems/LandauDichotomy.lean`, lines 24–28), the shifted-centre case is lines 91–133 (with `landau_nearest`, `landau_pole_asym` and the Cauchy estimate `landau_cauchy`, `LandauTheorems/LandauCauchy.lean`, lines 9–33, which applies Mathlib's `DifferentiableOn.hasFPowerSeriesOnBall` and `norm_cauchyPowerSeries_le` and is used at `landauWindow.lean`, line 114, and `LandauPoleAsym.lean`, line 52) and the real-pole case, with its positive residue, lines 134–165; both end in `landau_window_contra` (line 20), whose choice of a small $\eta > 0$, with the bound for every $k \ge U = \log Y$, is `Deduction.landau_growth_contra` (`LandauTheorems/LandauGrowthContra.lean`, lines 9–15). The library's other Landau-type criterion, `Formalism.HC.Landau.zero_free_of_Chebyshev_growth` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean`, line 538), which assumes the bound for all large $y$, is used there only through `Formalism.HC.level_of_tiedAll` and `Formalism.HC.zeroFreeOn_of_tiedAll` (`TotientGaloisClasses/TopWin.lean`, lines 117–134), on which the main theorems do not depend.
