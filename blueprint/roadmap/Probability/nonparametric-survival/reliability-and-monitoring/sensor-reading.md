# Sensor reading of a damage value with nonzero gain

For a gain $g \ne 0$, an offset $b$, a damage value $d$ and a sensor error $\varepsilon$, all real,
the sensor reading is

$$z = g\, d + b + \varepsilon,$$

a declared measurement model. The definition takes a proof of $g \ne 0$ as an argument, as the
[strain-gauge calibration](../../../Physics/quantities-and-measurement/strain-gauge-calibration-and-its-covariance/gauge-strain.md)
does, so a reading with zero gain is never formed; the value $g\, d + b + \varepsilon$ itself does
not use $g \ne 0$.
