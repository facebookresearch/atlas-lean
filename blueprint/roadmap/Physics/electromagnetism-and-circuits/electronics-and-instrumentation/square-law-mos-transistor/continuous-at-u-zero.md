# For $V_{DS} \ge 0$ the current is continuous in $u$ at the threshold

Let $\beta > 0$ and $V_{DS} \ge 0$. Then the [square-law drain current](current.md)
$I(\beta, u, V_{DS})$ ($0$ for $u \le 0$, the [triode formula](triode-current.md) for $u > 0$ and
$V_{DS} \le u$, the [saturation formula](saturation-current.md) for $u > 0$ and $V_{DS} > u$) is
continuous in the overdrive $u$ at $u = 0$, with $V_{DS}$ fixed: as $u \to 0$ from either side the
current tends to the cutoff value $0$ (it lies between $0$ and $\beta u^2 / 2$). The condition
$V_{DS} \ge 0$ cannot be dropped: for $\beta = 1$ and $V_{DS} = -1$ the current is $-u - 1/2$ for
$u > 0$, which tends to $-1/2$. In the physical reading $\beta > 0$ is the device constant,
$u = V_{GS} - V_{th}$ the gate overdrive and $V_{DS} \ge 0$ the drain–source voltage of a
forward-biased nMOS transistor.
