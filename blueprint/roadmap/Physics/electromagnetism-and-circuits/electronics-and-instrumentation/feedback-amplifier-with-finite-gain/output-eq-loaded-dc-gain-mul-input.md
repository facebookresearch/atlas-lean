# If $1 + \beta b A_0 \ne 0$, the DC output is the DC gain times $v_i$

Let $A_0$, $\omega_p$, $\beta$, $a$, $b$ be real numbers with $\omega_p \ne 0$ and
$1 + \beta b A_0 \ne 0$, and let the complex numbers $v_i$ (input), $v_{amp}$ (unloaded amplifier
output) and $v_o$ (loaded output) satisfy the loaded model equations at $s = 0$:

$$v_{amp} = A(0)\,(a v_i - \beta v_o), \qquad v_o = b\, v_{amp},$$

where $A(0) = A_0 / (1 + 0/\omega_p) = A_0$ is the [one-pole open-loop response](open-loop-gain.md)
at $s = 0$. Then

$$v_o = \frac{a b A_0}{1 + \beta b A_0}\, v_i,$$

the [loaded DC gain](loaded-dc-gain.md) times the input. At $s = 0$ the open-loop denominator is
$1$ and the loaded denominator is $1 + \beta b A_0$, so this is the case $s = 0$ of the
[loaded transfer theorem](output-eq-loaded-transfer-mul-input.md). In the model $A_0$, $\omega_p$
and $\beta$ are positive and so are the dividers $a$ and $b$; then $1 + \beta b A_0 > 1$, and both
conditions hold.
