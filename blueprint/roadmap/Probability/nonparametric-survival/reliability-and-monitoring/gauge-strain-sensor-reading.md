# The calibrated reading is the damage plus the error over the gain

For a gain $g \ne 0$ and all real $b$, $d$ and $\varepsilon$, applying the
[strain-gauge calibration](../../../Physics/quantities-and-measurement/strain-gauge-calibration-and-its-covariance/gauge-strain.md)
$V \mapsto (V - b) / g$ to the [sensor reading](sensor-reading.md) $z = g\, d + b + \varepsilon$
gives

$$\frac{z - b}{g} = d + \frac{\varepsilon}{g}:$$

the calibration recovers the damage up to the sensor error scaled by $1 / g$; it does not remove the
error.
