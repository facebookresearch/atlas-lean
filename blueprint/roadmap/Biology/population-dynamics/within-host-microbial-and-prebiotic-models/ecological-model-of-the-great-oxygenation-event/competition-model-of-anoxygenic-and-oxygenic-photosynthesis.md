# Competition model of anoxygenic and oxygenic photosynthesis

Let $x_1 \ge 0$ be the abundance of anoxygenic photosynthetic bacteria, $x_2 \ge 0$ that of
cyanobacteria, $y_1 \ge 0$ the concentration of a reductant (iron(II), or another electron donor
such as $\mathrm{H}_2$ or $\mathrm{H}_2\mathrm{S}$), $y_2 \ge 0$ that of phosphate and $z \ge 0$
that of dioxygen. With rate constants scaled to one wherever that is possible without loss of
generality, the dynamics are

$$\begin{aligned}
\dot x_1 &= x_1 y_1 y_2 - x_1 + u_1, \\
\dot x_2 &= c\,x_2 y_2 - x_2 + u_2, \\
\dot y_1 &= f_1 - y_1 - x_1 y_1 y_2 - y_1 z, \\
\dot y_2 &= f_2 - y_2 - x_1 y_1 y_2 - x_2 y_2, \\
\dot z &= a\,x_2 y_2 - b z - y_1 z,
\end{aligned}$$

with positive parameters: $c$ the reproduction rate of cyanobacteria, $f_1$ and $f_2$ the influxes
of reductant and phosphate, $a$ the biogenic production of oxygen, $b$ its geochemical consumption,
and $u_1, u_2 \ge 0$ small migration rates from refugia (taken to be negligible in the analysis
below). Anoxygenic bacteria need both the reductant and phosphate to reproduce; cyanobacteria need
only phosphate, and produce oxygen, which oxidizes the reductant.

## Remarks

The model is written so that redox balance holds by construction: every unit of reductant consumed
in anoxygenic photosynthesis leaves the pool $y_1$, and oxygen produced by cyanobacteria is removed
both geochemically, at rate $b z$, and by reaction with the reductant, at rate $y_1 z$. Since the
planet changes slowly compared with microbial generations, the Great Oxygenation Event is analysed
as a change of stability of the fixed points of this system as $f_1$ falls or $f_2$ rises.

## Sources

- J. Olejarz, Y. Iwasa, A. H. Knoll, M. A. Nowak, "The Great Oxygenation Event as a consequence of
  ecological dynamics modulated by planetary change", Nature Communications 12 (2021) 3985,
  Eq. (1), <https://doi.org/10.1038/s41467-021-23286-7> (PMC8238953).
