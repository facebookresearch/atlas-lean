# Strain read from an affine gauge calibration with nonzero gain

For a gain $g \ne 0$, an offset $b$ and a voltage $V$, all real, the strain bound by the affine
calibration $V = g\,\varepsilon + b$ is

$$
\varepsilon = \frac{V - b}{g}.
$$

A proof of $g \ne 0$ is an argument of the definition, so the strain is defined only for a nonzero
gain and no division by zero occurs. It is the only solution of $V = g\,\varepsilon + b$:
[gain times strain plus offset gives back the voltage](gauge-voltage-gauge-strain.md), and
[the calibration recovers the strain from its voltage](gauge-strain-gauge-voltage.md). In the
physical reading $V$, $b$ and $g$ are voltages, $g$ in volts per unit strain, and $\varepsilon$ is
dimensionless; the definition uses only $g \ne 0$, so the sign of the gain is not restricted.
