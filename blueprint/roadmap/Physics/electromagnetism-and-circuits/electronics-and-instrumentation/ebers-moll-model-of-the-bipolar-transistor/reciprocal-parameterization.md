# Reciprocity is equivalent to a common transport saturation current

Let $I_{SF}$, $I_{SR}$, $\alpha_F$, $\alpha_R$, $V_{BE}$ and $V_{BC}$ be real numbers with
$\alpha_F \neq 0$ and $\alpha_R \neq 0$, let $V_T > 0$, and write $u = e^{V_{BE}/V_T}$ and
$w = e^{V_{BC}/V_T}$. The reciprocity relation $\alpha_F I_{SF} = \alpha_R I_{SR}$ holds if and only
if there is a real number $I_S$ with $I_S = \alpha_F I_{SF}$, $I_{SF} = I_S / \alpha_F$ and
$I_{SR} = I_S / \alpha_R$ for which the [collector current](collector-current.md) and the
[emitter current](emitter-current.md) at $(V_{BE}, V_{BC})$ take the transport form

$$I_C = I_S (u - w) - I_S \frac{1 - \alpha_R}{\alpha_R} (w - 1) ,$$

$$I_E = I_S (u - w) + I_S \frac{1 - \alpha_F}{\alpha_F} (u - 1) .$$

So under reciprocity both saturation currents derive from the single transport saturation current
$I_S = \alpha_F I_{SF} = \alpha_R I_{SR}$, and the two currents depend on $I_{SF}$ and $I_{SR}$ only
through $I_S$. The equivalence does not derive reciprocity from device physics: it states what
reciprocity means for the currents.
