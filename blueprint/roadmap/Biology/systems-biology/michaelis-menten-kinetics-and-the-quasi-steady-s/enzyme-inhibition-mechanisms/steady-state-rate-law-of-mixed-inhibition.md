# Steady-state rate law of mixed inhibition

If the enzyme forms of the restricted mixed-inhibition mechanism are stationary at fixed free substrate and inhibitor, their product rate has the mixed-inhibition form. Its operational inhibition constants equal the two inhibitor dissociation constants for this mechanism; that identification is derived, not assumed.

Let $k_1, k_2, k_3, k_{-3}, k_4, k_{-4}>0$ and $k_{-1}\ge0$ be the rate constants of the
[mixed-inhibition mechanism](mixed-inhibition-mechanism.md). Write the
[Michaelis constant](../michaelis-constant.md) $K_M=(k_{-1}+k_2)/k_1$ and the elementary dissociation
constants $K_{EI}=k_{-3}/k_3$ and $K_{ES.I}=k_{-4}/k_4$. Let $e_T>0$ and fixed **free** concentrations
$s\ge0$, $i\ge0$.

*Steady-state premise.* The enzyme forms $(e,c,y,z)$ satisfy the complex equations with $s$ and $i$
frozen, and enzyme conservation:

$$
k_1es-(k_{-1}+k_2)c-k_4ci+k_{-4}z=0,\qquad k_3ei-k_{-3}y=0,\qquad k_4ci-k_{-4}z=0,
$$

$$
e+c+y+z=e_T.
$$

Then the system has exactly one solution,

$$
e=\frac{e_T}{1+s/K_M+i/K_{EI}+si/(K_MK_{ES.I})},\qquad c=\frac{s}{K_M}e,\qquad y=\frac{i}{K_{EI}}e,\qquad z=\frac{i}{K_{ES.I}}c,
$$

all nonnegative with $e>0$, and the product rate $v=k_2c$ is

$$
v=\frac{k_2e_Ts}{K_M(1+i/K_{EI})+s(1+i/K_{ES.I})}.
$$

The apparent catalytic and specificity constants, defined by
$k_0^{\mathrm{app}}=\lim_{s\to\infty}v/e_T$ and
$k_A^{\mathrm{app}}=\lim_{s\to0^+}v/(e_Ts)$, are

$$
k_0^{\mathrm{app}}=\frac{k_2}{1+i/K_{ES.I}},\qquad k_A^{\mathrm{app}}=\frac{k_2/K_M}{1+i/K_{EI}}.
$$

The IUBMB operational constants $K_{ic},K_{iu}$ are defined by the slopes in
$1/k_A^{\mathrm{app}}=(1/k_A)(1+i/K_{ic})$ and
$1/k_0^{\mathrm{app}}=(1/k_0)(1+i/K_{iu})$, where $k_A=k_2/K_M$ and $k_0=k_2$ are the values at $i=0$.
Comparison therefore gives $K_{ic}=K_{EI}$ and $K_{iu}=K_{ES.I}$ **for this mechanism**.
The inhibition is linear and mixed as a function of **free inhibitor $i$**. It is predominantly
competitive when $K_{ic}<K_{iu}$, pure noncompetitive when $K_{ic}=K_{iu}$, and predominantly
uncompetitive when $K_{ic}>K_{iu}$. With total inhibitor as the experimental variable, depletion can
change the apparent classification. For the uncompetitive mechanism ($k_3=k_{-3}=0$, no $EI$),
separate elimination gives $v=k_2e_Ts/(K_M+s(1+i/K_{ES.I}))$.

## Depends on

- [Mixed-inhibition mechanism](mixed-inhibition-mechanism.md)
- [Michaelis constant](../michaelis-constant.md)

## Proof depends on

- [Mixed-inhibition mechanism](mixed-inhibition-mechanism.md)
- [Michaelis constant](../michaelis-constant.md)

## Expansion

The $z$ equation gives $z=(i/K_{ES.I})c$; substituting it into the $c$ equation cancels the two
$ESI$ terms, leaving $k_1es=(k_{-1}+k_2)c$, so $c=(s/K_M)e$. The $y$ equation gives
$y=(i/K_{EI})e$. Conservation fixes $e$ through a positive bracket. Each dead-end inhibitor complex
is attached by one reversible pair; its stationarity makes that pair's net flux zero. Thus the
inhibitor-binding ratios hold exactly at the frozen steady state, without assuming fast binding.
The catalytic route does not impose substrate-binding equilibrium, which is why $K_M$, not
$K_S=k_{-1}/k_1$, appears. The two limits give the apparent constants, and comparison with IUBMB
Equations (21)–(22) gives the operational constants.

The law is not an identity along arbitrary trajectories. Equality of the product rate at one instant
need not make the other enzyme forms stationary. Nor does a mixed rate law identify this mechanism:
mechanisms in which inhibitor binds only the active site can produce mixed patterns.

## Sources

- A. Pesaresi, "Mixed and non-competitive enzyme inhibition: underlying mechanisms and mechanistic
  irrelevance of the formal two-site model", *Journal of Enzyme Inhibition and Medicinal Chemistry*
  38(1) (2023) 2245168, Introduction and caption of Figure 1 (binding to free enzyme and the ES complex,
  and the pure noncompetitive case $K_{IC}=K_{IU}$),
  <https://doi.org/10.1080/14756366.2023.2245168>. The caption and text, not the figure image, were read;
  the restricted mechanism's omitted $EI+S\rightleftharpoons ESI$ step is an explicit model choice.
- NC-IUB Panel on Enzyme Kinetics (A. Cornish-Bowden, H. B. F. Dixon, K. J. Laidler, I. H. Segel,
  J. Ricard, S. F. Velick and E. C. Webb), "Symbolism and terminology in enzyme kinetics,
  Recommendations 1981", *European Journal of Biochemistry* 128 (1982) 281–291; web version
  Section 6.4, Equations (21)–(22) and the subdivision of mixed inhibition,
  <https://iubmb.qmul.ac.uk/kinetics/ek4t6.html>.
- J. Eilertsen, S. Schnell and S. Walcher, *Bulletin of Mathematical Biology* 85 (2023), article 48, <https://doi.org/10.1007/s11538-023-01150-7>; locators from the version read, arXiv:2211.10836v2 (2023), Section 6.2, Equation (68)
  (uncompetitive reduction), <https://arxiv.org/abs/2211.10836v2>.
