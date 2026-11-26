# One-pole open-loop response $A_0/(1 + s/\omega_p)$

For real numbers $A_0$ and $\omega_p$ and a complex frequency $s$, the one-pole open-loop response
is

$$A(s) = \frac{A_0}{1 + s/\omega_p},$$

computed in the complex numbers with the convention $z / 0 = 0$. So for $\omega_p = 0$ it equals
$A_0$ for every $s$ (since $s / 0 = 0$), and for $\omega_p \ne 0$ it is $0$ at $s = -\omega_p$,
where its denominator vanishes. In every case $A(0) = A_0$. In the model $A_0 > 0$ is the DC gain
of the amplifier and $\omega_p > 0$ the angular frequency of its pole at $s = -\omega_p$.
