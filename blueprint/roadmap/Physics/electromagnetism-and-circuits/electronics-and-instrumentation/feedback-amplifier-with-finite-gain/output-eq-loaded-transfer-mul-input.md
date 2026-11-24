# Away from denominator zeros the loaded model gives $v_o = G(s)\,v_i$

Let $A_0$, $\omega_p$, $\beta$, $a$, $b$ be real numbers with $\omega_p \ne 0$, and let $s$ be a
complex frequency at which both denominators of the model are nonzero:

$$1 + s/\omega_p \ne 0 \qquad \text{and} \qquad 1 + s/\omega_p + \beta b A_0 \ne 0 .$$

Let the complex numbers $v_i$ (input), $v_{amp}$ (unloaded amplifier output) and $v_o$ (loaded
output) satisfy the two model equations

$$v_{amp} = A(s)\,(a v_i - \beta v_o), \qquad v_o = b\, v_{amp},$$

where $A(s) = A_0 / (1 + s/\omega_p)$ is the [one-pole open-loop response](open-loop-gain.md) and
$a v_i - \beta v_o$ is the feedback error. Then

$$v_o = G(s)\, v_i, \qquad G(s) = \frac{a b A_0}{1 + s/\omega_p + \beta b A_0},$$

where $G$ is the [loaded closed-loop transfer](loaded-transfer.md). In the model, $a$ and $b$ are
the [source divider](source-divider.md) and the [load divider](load-divider.md), $\beta$ is the
feedback factor applied to the loaded output, and $A_0, \omega_p > 0$. The proof clears the
open-loop denominator, combines the two equations into
$v_o\,(1 + s/\omega_p + \beta b A_0) = a b A_0\, v_i$, and divides by the loaded denominator.
