# Transconductance times thermal voltage at any bias

Let $I_{SF}$, $I_{SR}$, $\alpha_F$, $V_{BE}$ and $V_{BC}$ be real numbers and $V_T > 0$, and let
$g_m = \alpha_F I_{SF} e^{V_{BE}/V_T} / V_T$ be the
[transconductance](has-deriv-at-collector-current-vbe.md), the derivative of the collector current
in the base-emitter voltage. Then at every bias, whatever the signs of $V_{BE}$ and $V_{BC}$,

$$g_m V_T = I_C + I_R + \alpha_F I_{SF} ,$$

where $I_C$ is the [collector current](collector-current.md) and $I_R$ the
[reverse branch current](reverse-branch-current.md) at $(V_{BE}, V_{BC})$. At $V_T = 0$, which the
hypothesis excludes, the left side would be $0$ by the convention $a / 0 = 0$ while the right side
is $\alpha_F I_{SF}$.
