# Loaded closed-loop transfer $a b A_0/(1 + s/\omega_p + \beta b A_0)$

For real numbers $A_0$, $\omega_p$, $\beta$, $a$, $b$ and a complex frequency $s$, the loaded
closed-loop transfer is

$$G(s) = \frac{a b A_0}{1 + s/\omega_p + \beta b A_0},$$

computed in the complex numbers with the convention $z / 0 = 0$. It is $0$ where the loaded
denominator $1 + s/\omega_p + \beta b A_0$ vanishes; for $\omega_p > 0$ this happens exactly at
$s = -\omega_p (1 + \beta b A_0)$ ([denominator-zero characterisation](denominator-eq-zero-iff.md)).
For $\omega_p = 0$, where $s / 0 = 0$, it is the constant $a b A_0 / (1 + \beta b A_0)$, itself $0$
when $1 + \beta b A_0 = 0$.

In the model, $A_0 > 0$ and $\omega_p > 0$ describe the
[one-pole open-loop response](open-loop-gain.md) $A_0 / (1 + s/\omega_p)$, $\beta > 0$ is the
feedback factor, and $a$ and $b$ are the [source divider](source-divider.md) and the
[load divider](load-divider.md), both positive and at most $1$. For $\omega_p \ne 0$, signals
obeying the two model equations satisfy $v_o = G(s)\, v_i$ wherever neither the open-loop
denominator $1 + s/\omega_p$ nor the loaded denominator vanishes
([loaded transfer theorem](output-eq-loaded-transfer-mul-input.md)).
