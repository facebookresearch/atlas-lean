# Emitter current from a transport saturation current

Let $I_S$, $\alpha_F$, $\alpha_R$, $V_T$, $V_{BE}$ and $V_{BC}$ be real numbers with
$\alpha_F \neq 0$ and $\alpha_R \neq 0$, and write $u = e^{V_{BE}/V_T}$ and $w = e^{V_{BC}/V_T}$.
With the saturation currents $I_{SF} = I_S / \alpha_F$ and $I_{SR} = I_S / \alpha_R$, which satisfy
the reciprocity relation $\alpha_F I_{SF} = \alpha_R I_{SR} = I_S$, the
[emitter current](emitter-current.md), counted out of the emitter, is

$$I_E = I_S (u - w) + I_S \frac{1 - \alpha_F}{\alpha_F} (u - 1) ,$$

a formula in $I_S$ alone. No condition on $V_T$ is needed: at $V_T = 0$, with the convention
$a / 0 = 0$, both sides are $0$. In the device $I_S > 0$, $V_T > 0$ and the gains lie in $(0, 1)$.
