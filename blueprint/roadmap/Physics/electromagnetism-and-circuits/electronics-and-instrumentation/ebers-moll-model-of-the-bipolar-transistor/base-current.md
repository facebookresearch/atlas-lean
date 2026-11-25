# Base current of the Ebers–Moll model

For real numbers $I_{SF}$, $I_{SR}$ (the forward and reverse saturation currents), $\alpha_F$,
$\alpha_R$ (the forward and reverse common-base current gains), $V_T$ (the thermal voltage),
$V_{BE}$ and $V_{BC}$ (the base-emitter and base-collector voltages), the base current, counted
positive into the base, is

$$I_B = (1 - \alpha_F) I_F + (1 - \alpha_R) I_R ,$$

where $I_F = I_{SF} (e^{V_{BE}/V_T} - 1)$ and $I_R = I_{SR} (e^{V_{BC}/V_T} - 1)$ are the
[forward](forward-branch-current.md) and [reverse](reverse-branch-current.md) branch currents. It is
defined by this formula, not as a difference of the other two terminal currents; the
[terminal current balance](collector-add-base-add-emitter-out-eq.md) then shows $I_B = I_E - I_C$.
It is $0$ when $\alpha_F = \alpha_R = 1$, and, with the convention $a / 0 = 0$, at $V_T = 0$. In the
device $V_T > 0$, the saturation currents are positive and the gains lie in $(0, 1)$; the definition
accepts any real inputs.
