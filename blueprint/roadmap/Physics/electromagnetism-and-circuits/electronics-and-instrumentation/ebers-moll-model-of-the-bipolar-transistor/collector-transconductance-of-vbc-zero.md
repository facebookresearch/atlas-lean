# Transconductance from collector current at zero base-collector voltage

Let $I_{SF}$, $I_{SR}$, $\alpha_F$ and $V_{BE}$ be real numbers and $V_T > 0$. At zero
base-collector voltage $V_{BC} = 0$, the edge of forward-active operation, the
[transconductance](has-deriv-at-collector-current-vbe.md) is given by the
[collector current](collector-current.md) $I_C$ at $(V_{BE}, 0)$:

$$g_m = \frac{\alpha_F I_{SF}}{V_T}\, e^{V_{BE}/V_T} = \frac{I_C + \alpha_F I_{SF}}{V_T} .$$

So $g_m - I_C / V_T = \alpha_F I_{SF} / V_T$: the textbook value $I_C / V_T$ omits the term
$\alpha_F I_{SF} / V_T$.
