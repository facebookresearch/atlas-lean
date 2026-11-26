# Square-law activation of KCNQ channels by PIP2

Let $c(t)$ be the free membrane density of phosphatidylinositol 4,5-bisphosphate ($\mathrm{PIP}_2$)
and suppose binding to a channel site equilibrates fast compared with changes in $c$, with
dissociation constant $K_d > 0$, so the bound fraction is

$$b(t) = \frac{c(t)}{K_d + c(t)} .$$

In the square-law model the KCNQ2/3 current, relative to its maximum, is

$$\frac{I(t)}{I_{\max}} = b(t)^2 .$$

Consequently, if a readout proportional to $b$ falls as $b(t) = b_0 e^{-t/\tau}$ during depletion,
the current falls as $b_0^2 e^{-2t/\tau}$, with time constant $\tau/2$; and if $b$ recovers as
$b(t) = 1 - e^{-t/\tau}$, the current recovers as $(1 - e^{-t/\tau})^2$, an S-shaped curve with
zero initial slope and an inflection point at $t = \tau \ln 2$.

## Expansion

Squaring an exponential doubles its rate, which explains why, when the lipid is removed by a
voltage-sensitive phosphatase, current inhibition is faster than the loss of the lipid reported by
a fluorescent pleckstrin-homology probe. For recovery, $y = (1 - e^{-s})^2$ with $s = t/\tau$ has
$y' \propto (1 - e^{-s})e^{-s}$, which vanishes at $s = 0$, and $y'' \propto e^{-s}(2e^{-s} - 1)$,
which vanishes at $e^{-s} = 1/2$; a single-exponential fit to this sigmoid gives a time constant
longer than $\tau$. The exponent $2$ is a Hill-type cooperativity; the source finds fits nearly
as good with an exponent of $1.8$ and a lower $K_d$, consistent with Hill coefficients of about
$1.35$ to $1.9$ measured with soluble lipid analogs. Fast binding (residence times below
$10$ ms) justifies treating $b$ as an instantaneous function of $c$.

## Sources

- B. H. Falkenburger, J. B. Jensen, B. Hille, "Kinetics of PIP2 metabolism and KCNQ2/3 channel
  regulation studied with a voltage-sensitive phosphatase in living cells", Journal of General
  Physiology 135 (2010), Results (square law relating current to probe FRET, Fig. 4) and
  the kinetic model (KCNQ current $= (\mathrm{KCNQ\_PIP_2})^2$),
  <https://doi.org/10.1085/jgp.200910345> (PMC2812502).
