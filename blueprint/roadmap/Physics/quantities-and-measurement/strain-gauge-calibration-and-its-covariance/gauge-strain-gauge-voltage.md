# The calibration recovers the strain from its voltage

For a gain $g \ne 0$, an offset $b$ and a strain $\varepsilon$, all real, the
[strain](gauge-strain.md) read from the voltage $g\,\varepsilon + b$ is $\varepsilon$:

$$
\frac{(g\,\varepsilon + b) - b}{g} = \varepsilon.
$$

With [gain times strain plus offset gives back the voltage](gauge-voltage-gauge-strain.md), the maps
$\varepsilon \mapsto g\,\varepsilon + b$ and $V \mapsto (V - b)/g$ are inverse bijections of the
real line.
