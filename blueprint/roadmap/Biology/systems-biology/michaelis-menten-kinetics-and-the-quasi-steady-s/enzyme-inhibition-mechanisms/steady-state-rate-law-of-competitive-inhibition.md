# Steady-state rate law of competitive inhibition

If the enzyme forms of the competitive mechanism are held at their steady state for given free substrate and free inhibitor, the product rate is $v = k_2 e_T s/(K_M(1 + i/K_I) + s)$. This is a conditional rate law under a stated steady-state premise, not an identity along trajectories.

Let $k_1, k_2, k_3, k_{-3} > 0$ and $k_{-1} \ge 0$ be the rate constants of the
[competitive-inhibition mechanism](competitive-inhibition-mechanism.md), with the
[Michaelis constant](../michaelis-constant.md) $K_M = (k_{-1} + k_2)/k_1$ and $K_I = k_{-3}/k_3$.
Let $e_T > 0$ (total enzyme) and let $s \ge 0$, $i \ge 0$ be fixed **free** substrate and inhibitor
concentrations.

*Steady-state premise.* The enzyme forms $(e, c, y)$ satisfy the complex equations of the mechanism
with $s$ and $i$ frozen, and enzyme conservation:

$$k_1 e s - (k_{-1} + k_2)\, c = 0, \qquad k_3 e i - k_{-3}\, y = 0, \qquad e + c + y = e_T .$$

Then this linear system has exactly one solution,

$$e = \frac{e_T}{1 + s/K_M + i/K_I}, \qquad c = \frac{s}{K_M}\, e, \qquad y = \frac{i}{K_I}\, e,$$

all nonnegative with $e > 0$, and the product rate $v = k_2 c$ is

$$v = \frac{k_2\, e_T\, s}{K_M\,(1 + i/K_I) + s},$$

the [Michaelis–Menten rate law](../mm-rate.md) with $V_{\max} = k_2 e_T$ and apparent Michaelis
constant $K_M(1 + i/K_I)$.

In the operational terms of the IUBMB recommendations, with catalytic constant
$k_0 = \lim_{s \to \infty} v/e_T$ and specificity constant $k_A = \lim_{s \to 0^+} v/(e_T s)$, the
apparent values at inhibitor level $i$ are $k_0^{\mathrm{app}} = k_2$, independent of $i$, and
$1/k_A^{\mathrm{app}} = (K_M/k_2)(1 + i/K_I)$. So the inhibition is competitive **as a function of free inhibitor $i$**, linear, with
competitive inhibition constant $K_{ic} = K_I$; in this mechanism $K_{ic}$ is the dissociation
constant of $EI$. The Michaelis constant is not the substrate dissociation constant:
$K_M = K_S + k_2/k_1 > K_S = k_{-1}/k_1$.

## Depends on

- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)
- [Michaelis constant](../michaelis-constant.md)
- [Michaelis–Menten rate law](../mm-rate.md)

## Proof depends on

- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)

## Expansion

The first two equations give $c = (s/K_M)e$ and $y = (i/K_I)e$ because $k_1, k_3 > 0$ and
$k_{-1} + k_2 > 0$, $k_{-3} > 0$. Substituting into the conservation law gives
$e(1 + s/K_M + i/K_I) = e_T$ with a positive bracket, hence uniqueness, and $v = k_2 c$ simplifies to
the stated law after multiplying numerator and denominator by $K_M$. The limits $s \to \infty$ and
$s \to 0^+$ give $k_0^{\mathrm{app}}$ and $k_A^{\mathrm{app}}$, which is IUBMB Eq. (21) with
$K_{ic} = K_I$ and no uncompetitive term of Eq. (22).

The premise is an assumption about the regime: it freezes $s$ and $i$, which the full mass-action
system does not do, and the law fails off the steady state, for instance at the start of a reaction
([rate laws fail off the steady state](inhibited-rate-laws-fail-off-the-steady-state.md)). In the
limit of small total enzyme with the other parameters fixed, Eilertsen, Schnell and Walcher obtain the
same expression as the singular-perturbation reduction of the substrate equation, with the free
inhibitor replaced by the total inhibitor $i_0$; for finite enzyme the
[total-inhibitor form](competitive-steady-state-in-total-inhibitor.md) differs. The rate law alone
does not identify the mechanism ([see this example](competitive-law-does-not-determine-mechanism.md)).

## Sources

- Nomenclature Committee of the International Union of Biochemistry (NC-IUB), Panel on Enzyme
  Kinetics (A. Cornish-Bowden, H. B. F. Dixon, K. J. Laidler, I. H. Segel, J. Ricard, S. F. Velick and
  E. C. Webb), "Symbolism and terminology in enzyme kinetics, Recommendations 1981", *European Journal
  of Biochemistry* 128 (1982) 281–291; web version Sections 4.1–4.2, Eqs. (8)–(11) (limiting rate
  constants $k_A$, $k_0$; the Michaelis constant, or Michaelis concentration, "is not, in general, an
  equilibrium constant"),
  Section 6.2 and Section 6.4, Eqs. (21)–(22), <https://iubmb.qmul.ac.uk/kinetics/ek4t6.html>.
- J. Eilertsen, S. Schnell and S. Walcher, *Bulletin of Mathematical Biology* 85 (2023), article 48, <https://doi.org/10.1007/s11538-023-01150-7>; locators from the version read, arXiv:2211.10836v2 (2023), Section 6.3, Eq. (77),
  <https://arxiv.org/abs/2211.10836v2>.
