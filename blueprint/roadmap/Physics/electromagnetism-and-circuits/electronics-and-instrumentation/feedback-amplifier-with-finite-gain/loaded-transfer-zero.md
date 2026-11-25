# At $s = 0$ the loaded transfer equals the loaded DC gain

For all real numbers $A_0$, $\omega_p$, $\beta$, $a$, $b$, the
[loaded closed-loop transfer](loaded-transfer.md) at $s = 0$ is the
[loaded DC gain](loaded-dc-gain.md), viewed as a complex number:

$$G(0) = \frac{a b A_0}{1 + \beta b A_0} .$$

The identity holds for every parameter choice because both sides use the same division, and
$0 / \omega_p = 0$ for every $\omega_p$, including $\omega_p = 0$. When $1 + \beta b A_0 = 0$ both
sides are $0$ by the convention $x / 0 = 0$, and no gain of the model is claimed there. When
$1 + \beta b A_0 \ne 0$, the [DC output of the loaded model](output-eq-loaded-dc-gain-mul-input.md)
is this gain times the input.
