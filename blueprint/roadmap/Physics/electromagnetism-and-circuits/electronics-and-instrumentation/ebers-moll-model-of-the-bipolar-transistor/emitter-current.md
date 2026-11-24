# Emitter current of the Ebers–Moll model

For real numbers $I_{SF}$, $I_{SR}$ (the forward and reverse saturation currents), $\alpha_R$ (the
reverse common-base current gain), $V_T$ (the thermal voltage), $V_{BE}$ and $V_{BC}$ (the
base-emitter and base-collector voltages), the emitter current, counted positive out of the
emitter, is

$$I_E = I_F - \alpha_R I_R ,$$

where $I_F = I_{SF} (e^{V_{BE}/V_T} - 1)$ and $I_R = I_{SR} (e^{V_{BC}/V_T} - 1)$ are the
[forward](forward-branch-current.md) and [reverse](reverse-branch-current.md) branch currents.
The forward gain does not enter. With the convention $a / 0 = 0$, $V_T = 0$ gives
$I_F = I_R = 0$ and $I_E = 0$. In the device $V_T > 0$, the saturation currents are positive and
$0 < \alpha_R < 1$; the definition accepts any real inputs.
