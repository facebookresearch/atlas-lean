# Inhibited rate laws fail off the steady state

The steady-state laws of competitive and mixed inhibition are not identities along mass-action trajectories. At the start of a reaction with no complexes the product rate is zero while either law is positive. Agreement of the product rate at one instant constrains the catalytic complex alone, not stationarity of all enzyme forms.

Let $k_1, k_2, k_3, k_{-3} > 0$ and $k_{-1} \ge 0$, with $K_M = (k_{-1} + k_2)/k_1$ and
$K_I = k_{-3}/k_3$, and let $(s, i, e, c, y, p)$ solve the
[competitive-inhibition mechanism](competitive-inhibition-mechanism.md) on $[0, \infty)$ with total
enzyme $e_T = e(0) + c(0) + y(0) > 0$. Write

$$v_{\mathrm{ss}}(t) = \frac{k_2\, e_T\, s(t)}{K_M\,(1 + i(t)/K_I) + s(t)}$$

for the [competitive steady-state law](steady-state-rate-law-of-competitive-inhibition.md) evaluated
at the current free concentrations, defined whenever $s(t), i(t) \ge 0$. Then:

1. For every $t \ge 0$ with $s(t), i(t) \ge 0$, $p'(t) = v_{\mathrm{ss}}(t)$ if and only if
   $c(t) = e_T s(t)/(K_M(1 + i(t)/K_I) + s(t))$.
2. With the standard data $s(0) = s_0 > 0$, $i(0) = i_0 \ge 0$, $e(0) = e_T$ and
   $c(0) = y(0) = p(0) = 0$,

$$p'(0) = 0 < \frac{k_2\, e_T\, s_0}{K_M\,(1 + i_0/K_I) + s_0} = v_{\mathrm{ss}}(0), \qquad c'(0) = k_1 e_T s_0 > 0 .$$

The same holds for the [mixed-inhibition mechanism](mixed-inhibition-mechanism.md) with
$k_4, k_{-4} > 0$, $K_{EI}=k_{-3}/k_3$, $K_{ES.I}=k_{-4}/k_4$, total enzyme $e_T = e + c + y + z$ at $t = 0$ and the
[mixed steady-state law](steady-state-rate-law-of-mixed-inhibition.md): $p'(t)$ equals that law at
$(s(t), i(t))$ exactly when $c(t)$ equals
$e_T s(t)/(K_M(1 + i(t)/K_{EI}) + s(t)(1 + i(t)/K_{ES.I}))$, and at the standard data with $z(0) = 0$
the product rate is $0$ while the law is positive.

## Depends on

- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)
- [Mixed-inhibition mechanism](mixed-inhibition-mechanism.md)
- [Steady-state rate law of competitive inhibition](steady-state-rate-law-of-competitive-inhibition.md)
- [Steady-state rate law of mixed inhibition](steady-state-rate-law-of-mixed-inhibition.md)

## Proof depends on

- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)
- [Mixed-inhibition mechanism](mixed-inhibition-mechanism.md)
- [Conserved totals of the inhibition mechanisms](conserved-totals-of-inhibition-mechanisms.md)

## Expansion

The product equation of either mechanism is $p' = k_2 c$, and $k_2 > 0$, so $p'(t)$ equals a law of
the form $k_2 \cdot (\text{steady-state } c)$ exactly when $c(t)$ equals that steady-state value; the
total enzyme in the law is the conserved total, constant along the solution. At the standard data
$c(0) = 0$, while the steady-state value $e_T s_0/(K_M(1 + i_0/K_I) + s_0)$ is positive because
$e_T, s_0 > 0$. The complex equation at $t = 0$ reads $c'(0) = k_1 e_T s_0 - 0 > 0$, so the
trajectory starts away from the frozen steady state. Applying the steady-state premise during a later phase requires a separate approximation argument; it is not an exact trajectory identity.

## Sources

- J. Eilertsen, S. Schnell and S. Walcher, "Natural parameter conditions for singular perturbations of
  chemical and biochemical reaction networks", *Bulletin of Mathematical Biology* 85 (2023), article 48, <https://doi.org/10.1007/s11538-023-01150-7>; locators from the version read, arXiv:2211.10836v2 (2023), Section 6.3, Eqs. (74),
  (75) and (77) (full competitive system with initial data $c_1(0) = c_2(0) = 0$, and its reduction)
  and Section 6.2, Eqs. (64), (65) and (68) (the uncompetitive reduction holds "in the limiting case of
  small" enzyme, up to errors of second order), <https://arxiv.org/abs/2211.10836v2>.
- The IUBMB recommendations describe the same distinction for one substrate: the steady-state
  approximation "is not valid during these early times" of pre-steady-state kinetics (NC-IUB Panel on
  Enzyme Kinetics, A. Cornish-Bowden, H. B. F. Dixon, K. J. Laidler, I. H. Segel, J. Ricard,
  S. F. Velick and E. C. Webb, "Symbolism and terminology in enzyme kinetics, Recommendations 1981",
  *European Journal of Biochemistry* 128 (1982) 281–291; web version Section 3.2, Eq. (7),
  <https://iubmb.qmul.ac.uk/kinetics/ek1t3.html>).
