# For positive overdrive the current at $V_{DS} = u$ is the common value

For all real $\beta$ and every $u > 0$, the [square-law drain current](current.md)
$I(\beta, u, V_{DS})$ ($0$ for $u \le 0$, the [triode formula](triode-current.md) for $u > 0$ and
$V_{DS} \le u$, the [saturation formula](saturation-current.md) for $u > 0$ and $V_{DS} > u$) at
$V_{DS} = u$ equals both the triode formula and the saturation formula there:

$$I(\beta, u, u) = \beta \left(u \cdot u - \frac{u^2}{2}\right) = \frac{\beta u^2}{2}.$$

For $u \le 0$ the current at $V_{DS} = u$ is the cutoff value $0$ instead. In the physical reading
$\beta > 0$ is the device constant, $u = V_{GS} - V_{th}$ the gate overdrive and $V_{DS} \ge 0$ the
drain–source voltage of a forward-biased nMOS transistor.
