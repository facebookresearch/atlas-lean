# Window bound for Tate–Shafarevich groups of Tate twists over subfields of cyclotomic fields

Let $E$ be a number field with algebraic closure $\bar E$, let $\ell$ be a prime and $n$ an integer.
Let $S$ be the set of places of $E$ above $\ell$ and the archimedean places, $E_S \subset \bar E$ the
maximal extension of $E$ unramified outside $S$, $G_{E,S} = \operatorname{Gal}(E_S/E)$, and
$\mathbb{Q}_\ell/\mathbb{Z}_\ell(n)$ the discrete group $\mathbb{Q}_\ell/\mathbb{Z}_\ell$ on which $G_{E,S}$
acts through the $n$-th power of the $\ell$-adic cyclotomic character. For each place $v \mid \ell$ of
$E$ choose a place $\bar v$ of $\bar E$ above $v$, with decomposition group
$D_{\bar v} \subset \operatorname{Gal}(\bar E/E)$ acting on $\mathbb{Q}_\ell/\mathbb{Z}_\ell(n)$ through its
image in $G_{E,S}$, and let

$$\text{Ш}^1_\ell(E, n) = \ker\Bigl(H^1\bigl(G_{E,S}, \mathbb{Q}_\ell/\mathbb{Z}_\ell(n)\bigr) \to \prod_{v \mid \ell} H^1\bigl(D_{\bar v}, \mathbb{Q}_\ell/\mathbb{Z}_\ell(n)\bigr)\Bigr),$$

in the cohomology of continuous cochains. It does not depend on the choices. For an integer
$t \ge 1$ and a real number $B$, say that $E$ satisfies $V(t, B)$ if, for every prime $\ell$ and every
integer $k$ with $1 \le k \le t - 1$, the group $\text{Ш}^1_\ell(E, -k)$ is finite, and

$$\sum_{\ell} \sum_{k=1}^{t-1} \log \# \text{Ш}^1_\ell(E, -k) \le B,$$

where $\ell$ runs over all primes. The terms are nonnegative, and the sum over $\ell$ is the supremum of
its finite partial sums: the inequality says that the partial sum over every finite set of primes is at
most $B$.

For a primitive Dirichlet character $\psi$ of conductor $N_\psi$, an integer $m \ge 0$ and odd primes
$q$ and $d$, call a number field $E$ a model of $K(\psi, m, q, d)$ if there are a common multiple $N$ of
$2^{m+2}$, $N_\psi$, $q$ and $d$, a primitive $N$-th root of unity $\zeta_N$ and a field embedding
$j \colon E \to \mathbb{Q}(\zeta_N)$ such that, for every automorphism $\tau$ of $\mathbb{Q}(\zeta_N)$ and
every integer $a \ge 0$ with $\tau(\zeta_N) = \zeta_N^a$, the automorphism $\tau$ fixes $j(E)$ pointwise
if and only if

$$a \equiv \pm 1 \pmod{2^{m+2}}, \qquad \psi(a) = 1, \qquad \Bigl(\frac{a}{q}\Bigr) = 1, \qquad \Bigl(\frac{a}{d}\Bigr) = 1,$$

where $(\tfrac{\cdot}{q})$ and $(\tfrac{\cdot}{d})$ are Legendre symbols. These conditions depend only on
the residue of $a$ modulo $N$, and $\tau$ determines that residue, since $\zeta_N$ has order $N$.

**Statement.** Let $\psi$ be a primitive Dirichlet character, let $0 < \varepsilon < 1/52$, and let
$m \colon [1, \infty) \to \mathbb{Z}_{\ge 0}$ be a function with
$x^{2 + 8\varepsilon} \le 2^{m(x)} \le 2 x^{2 + 8\varepsilon}$ for every $x \ge 1$. There are real numbers
$J \ge 1$ and $X_0 \ge 1$ with the following property. Let $X \ge X_0$, let $Z = X^{1/J}$, and let $q$ and
$d$ be primes such that

- $q \equiv 3 \pmod 8$ and $Z^{\varepsilon/5}/2 < \log q \le Z^{\varepsilon/5}$;
- $d \equiv 7 \pmod{16}$ and $Z^{\varepsilon/5} (\log Z)^2/2 < \log d \le Z^{\varepsilon/5} (\log Z)^2$;
- $q$ divides $d + 1$, and so does every odd prime $p \le Z^{\varepsilon/5}$.

Then there is a real number $Y$ with $Z \le Y$ and $Y^2 \le X$ such that, for every real $x$ with
$Y \le x \le Y^2$, every model of $K(\psi, m(x), q, d)$ satisfies
$V\bigl(\lfloor x^{401} \rfloor, \exp(x^\varepsilon/2)\bigr)$.

The models are totally imaginary: the automorphisms of $\mathbb{Q}(\zeta_N)$ commute, since each is
$\zeta_N \mapsto \zeta_N^a$ for some $a$, and complex conjugation, the automorphism with $a = N - 1$,
fixes $j(E)$ for no embedding $j$ as above because $(\tfrac{-1}{q}) = -1$ for $q \equiv 3 \pmod 4$.
Their archimedean places therefore have trivial decomposition groups, and
$\text{Ш}^1_\ell$ above is the kernel of localization at all the places of $S$. The statement bounds the
Tate–Shafarevich groups of the Tate twists $\mathbb{Q}_\ell/\mathbb{Z}_\ell(-k)$,
$1 \le k < \lfloor x^{401} \rfloor$, of every model of $K(\psi, m(x), q, d)$, uniformly for
the scales $x$ of a window $[Y, Y^2]$ with $Y \in [X^{1/J}, \sqrt{X}]$, so that
$[Y, Y^2] \subset [X^{1/J}, X]$, for every large $X$. It is the input from Galois cohomology of the
[window bounds for weighted Chebyshev sums of cyclic families of characters](../../distribution-of-primes/primes-in-progressions/chebyshev-window-bounds-for-cyclic-character-families.md).

## Depends on

- [Galois groups with restricted ramification and their modules](galois-cohomology-of-number-fields/galois-groups-with-restricted-ramification.md), for the Galois groups $G_{E,S}$ of the maximal extensions unramified outside $S$, their discrete modules and their cohomology
- [Tate–Shafarevich groups of Galois modules](galois-cohomology-of-number-fields/tate-shafarevich-groups.md), for Tate–Shafarevich groups; the groups $\text{Ш}^1_\ell(E, n)$ above impose local conditions at the places above $\ell$ only, and are those groups for the totally imaginary fields of the statement
- [Cyclotomic character and Tate twists](cyclotomic-character-and-tate-twists.md), for the twists $\mathbb{Q}_\ell/\mathbb{Z}_\ell(n)$
- [Primitive characters at divisor levels](../../zeta-l-functions/dirichlet-l-functions/conductors-and-primitive-dirichlet-characters/primitive-inducer.md), for the primitive character $\psi$ and its conductor $N_\psi$, its level (the case $d = m$ of a primitive inducer)

## Proof depends on

- [Galois representations attached to polarized regular algebraic cuspidal representations over CM fields](galois-representations-attached-to-polarized-cuspidal-representations.md), which supplies the Galois representations the argument uses
- [Derivation of the Tate–Shafarevich window bound from automorphic Galois representations](derivation-of-the-tate-shafarevich-window-bound.md), for the argument and its published inputs

## Sources

- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>); the Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited below by paths in it. The statement of this page is `UpperTheory.Top.VWin` with its auxiliary definitions `VVle` ($V(t, B)$), `IsChiField` (the models of $K(\psi, m, q, d)$ above, all of which `VAt` covers), `WinPair`, `PageN`, `VAt` and `VWinAt` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean`, lines 12–49), where the exponent $401$ is the argument of `VWinAt` in `VWin`. The groups $\text{Ш}^1_\ell(E, -k)$ are `Formalism.GaloisCohomology.Sha` for the twists `qzTw` (`src/Formalism/GaloisCohomology/Statement.lean`, lines 54–78), with local conditions at the places above $\ell$ only, and `VVle` requires the lengths `shaLen` to be finite and bounds the sum of $\log \ell$ times these $\mathbb{Z}_\ell$-lengths over every finite set of primes $\ell$ (`ExistsPageN.lean`, lines 12–17). The groups $G_{E,S}$ are `ReciprocityTheory.Gal.GS` (`src/ReciprocityTheory/GaloisValuations/Global.lean`, lines 128–145) and the cohomology is `ReciprocityTheory.Gal.H1`, by continuous cocycles (`src/ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean`, lines 42–66). The statement is proved as `UpperTheory.One.vwin_of_row` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean`, lines 4–5), which consumes the Galois representations as its hypothesis `h` and passes them, with base change `UpperTheory.BaseChangeIdentities.baseChangeN`, to the argument `UpperTheory.One.Join.automorphic_window_of_inputs` (`.../DenseThresholdCases/TopMainZj.lean`, lines 71–74), both directly and through `UpperTheory.LiteratureTheorems.OpenImageCondition.mk`. The statement is consumed by the window bounds for weighted Chebyshev sums at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean`, line 15.
