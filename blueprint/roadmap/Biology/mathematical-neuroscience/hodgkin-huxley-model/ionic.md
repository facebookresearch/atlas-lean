# Total ionic current of the Hodgkin–Huxley membrane

For a [parameter set](params.md) and real numbers $V, m, h, n$, the total ionic current is

$$I_{ion}(V, m, h, n) = g_{Na}\, m^3 h\,(V - E_{Na}) + g_K\, n^4\,(V - E_K) + g_L\,(V - E_L),$$

the sum of the sodium, potassium and leak currents, counted positive outward. The formula is taken
for all real arguments; in the model the conductances are nonnegative and the gating variables
$m, h, n$ lie in $[0, 1]$.
