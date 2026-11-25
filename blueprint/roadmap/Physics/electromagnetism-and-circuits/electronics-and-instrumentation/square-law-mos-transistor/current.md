# Piecewise square-law drain current with cutoff, triode and saturation

For real numbers $\beta$, $u$ and $V_{DS}$, the drain current of the ideal square-law nMOS model is
defined with the cutoff branch first:

$$I(\beta, u, V_{DS}) = \begin{cases} 0 & \text{if } u \le 0, \\
\beta \left(u\, V_{DS} - V_{DS}^2 / 2\right) & \text{if } u > 0 \text{ and } V_{DS} \le u, \\
\beta u^2 / 2 & \text{if } u > 0 \text{ and } V_{DS} > u, \end{cases}$$

the [triode formula](triode-current.md) and the [saturation formula](saturation-current.md) on the
active branches. At $V_{DS} = u > 0$ the triode branch is used; both formulas give $\beta u^2 / 2$
there. The definition covers all real inputs: for $u > 0$ the triode branch also applies to negative
$V_{DS}$, where the current is negative when $\beta > 0$ (for example $I(1, 1, -1) = -3/2$). In the
physical reading $\beta > 0$ is the device constant, $u = V_{GS} - V_{th}$ the gate overdrive and
$V_{DS} \ge 0$ the drain–source voltage of a forward-biased nMOS transistor; long-channel square
law, no channel-length modulation or body effect.
