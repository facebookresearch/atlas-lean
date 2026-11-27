# Dissolved-oxygen balance with interfacial transfer

The dissolved-oxygen concentration $C$ of a well-mixed liquid gains oxygen across the gas–liquid interface at the
volumetric rate $K_L a\,(C^* - C)$, the overall liquid-phase flux $K_L\,(C^* - C)$ times the interfacial area $a$ per
unit liquid volume. It loses oxygen to uptake at the rate $u(t)$ and is diluted at the rate $D(t)$ by a feed carrying
no oxygen. Let $K_L a > 0$ and $C^*$ be constants, let $u(t) \ge 0$ and $D(t) \ge 0$ for every $t$ in the horizon
$[0, T]$, and let $C$ solve

$$
C' = K_L a\,(C^* - C) - u(t) - D(t)\,C
$$

on $[0, T]$: $C$ is differentiable on $[0, T]$, with one-sided derivatives at the endpoints, and its derivative at
every $t \in [0, T]$ is given by this equation. Then:

1. If $u(t) \le K_L a\,C^*$ for every $t \in [0, T]$ and $C(0) \in [0, C^*]$, then $C(t) \in [0, C^*]$ for every
   $t \in [0, T]$.
2. For every $C_{\mathrm{crit}}$, if $C(0) \ge C_{\mathrm{crit}}$ and
   $K_L a\,(C^* - C_{\mathrm{crit}}) \ge u(t) + D(t)\,C_{\mathrm{crit}}$ for every $t \in [0, T]$, then
   $C(t) \ge C_{\mathrm{crit}}$ for every $t \in [0, T]$.
3. If $T \ge 0$ and $u = u_0$ and $D = D_0$ are constant on $[0, T]$, the pointwise condition of 2,
   $K_L a\,(C^* - C_{\mathrm{crit}}) \ge u(t) + D(t)\,C_{\mathrm{crit}}$ for every $t \in [0, T]$, holds if and only if
   $C_{\mathrm{eq}} = (K_L a\,C^* - u_0)/(K_L a + D_0) \ge C_{\mathrm{crit}}$.

In applications $C_{\mathrm{crit}}$ is a critical oxygen concentration with $0 \le C_{\mathrm{crit}} < C^*$, and
$C_{\mathrm{eq}}$ is the concentration at which the right-hand side vanishes for the constant inputs. The bounds need
no continuity of $u$ or $D$; continuity matters only for a solution to exist. The equation must hold at every
$t \in [0, T]$, so an input with a jump, such as a piecewise-constant feed, in general has no solution in this sense
across the jump, since a derivative has no jump discontinuities; the results then apply piece by piece, on each
interval between jumps, starting from the value the previous interval ends at. Each bound is a barrier argument:
$w = C - C_{\mathrm{crit}}$, or $w = C^* - C$ for the upper bound in 1, starts nonnegative and has $w' \ge 0$ wherever
$w < 0$, so it never becomes negative; the lower bound in 1 is 2 with $C_{\mathrm{crit}} = 0$. Using a $K_L a$ from an
interfacial mass-transfer correlation requires that correlation's assumptions; gas-phase dynamics are outside this
result.

## Sources

- L. Lamm and L. Jarboe, *Chemical Engineering Separations: A Handbook for Students*, LibreTexts, Section 1.2, overall liquid-phase transfer $N_A = K_L(c_A^* - c_{Ab})$, Equation 3.4, <https://eng.libretexts.org/Bookshelves/Chemical_Engineering/Chemical_Engineering_Separations%3A_A_Handbook_for_Students_(Lamm_and_Jarboe)/01%3A_Chapters/1.02%3A_Mass_Transfer_in_Gas-liquid_Systems>.
