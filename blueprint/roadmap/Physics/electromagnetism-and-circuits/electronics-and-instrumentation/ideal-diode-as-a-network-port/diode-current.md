# Ideal Shockley diode current

For real numbers $I_s$ (saturation current), $n$ (emission coefficient), $k_B$, $T$, $q$ and an
anode-to-cathode voltage $V$, the ideal Shockley diode current from anode to cathode is

$$I_D(V) = I_s \left(\exp\frac{V}{n V_T} - 1\right), \qquad V_T = \frac{k_B T}{|q|},$$

with $V_T$ the [thermal voltage](thermal-voltage.md). It is the
[exponential junction branch law](../ebers-moll-model-of-the-bipolar-transistor/forward-branch-current.md)
$I_s (\exp(V / V_0) - 1)$ at the scale $V_0 = n V_T$. With the convention $x / 0 = 0$, the scale
is $0$ when $n$, $k_B$, $T$ or $q$ is zero, and then $I_D(V) = I_s(e^0 - 1) = 0$ for every $V$;
for a negative scale the exponential $\exp(V / (n V_T))$ decreases in $V$. In the
physical reading $I_s > 0$, $n > 0$, $k_B > 0$, $T > 0$ and $q \ne 0$, so the scale is positive.
