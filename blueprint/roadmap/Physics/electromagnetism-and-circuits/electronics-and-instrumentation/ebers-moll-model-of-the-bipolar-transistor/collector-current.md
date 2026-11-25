# Collector current of the Ebers–Moll model

For real numbers $I_{SF}$, $I_{SR}$ (the forward and reverse saturation currents), $\alpha_F$ (the
forward common-base current gain), $V_T$ (the thermal voltage), $V_{BE}$ and $V_{BC}$ (the
base-emitter and base-collector voltages), the collector current, counted positive into the
collector, is

$$I_C = \alpha_F I_F - I_R ,$$

where $I_F = I_{SF} (e^{V_{BE}/V_T} - 1)$ and $I_R = I_{SR} (e^{V_{BC}/V_T} - 1)$ are the
[forward](forward-branch-current.md) and [reverse](reverse-branch-current.md) branch currents.
The reverse gain does not enter. With the convention $a / 0 = 0$, $V_T = 0$ gives
$I_F = I_R = 0$ and $I_C = 0$. In the device $V_T > 0$, the saturation currents are positive and
$0 < \alpha_F < 1$; the definition accepts any real inputs.
