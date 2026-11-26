# Strain vector of n gauges with nonzero gains

For $n$ gauges with gains $g_1, \dots, g_n$, all nonzero, offsets $b_1, \dots, b_n$ and voltages
$V_1, \dots, V_n$, the strain vector has, for each channel $i$, the [strain](gauge-strain.md)

$$
\varepsilon_i = \frac{V_i - b_i}{g_i}.
$$

A proof that every gain is nonzero is an argument of the definition, so no division by zero occurs.
