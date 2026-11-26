# For E, V, X_s > 0, the power–angle formulas of the synchronous generator model

Let $E > 0$, $V > 0$, $X_s > 0$ and $\delta \in \mathbb{R}$. Then the
[generator current](synchronous-current.md), directed out of the generator toward the bus, is

$$I = \frac{E\, e^{i\delta} - V}{i\, X_s},$$

and the [three-phase complex power](total-complex-power.md) $S = 3\, V\, \overline{I}$ at the
terminals (RMS phasors, terminal voltage $V$ real) satisfies

$$\operatorname{Re} S = \frac{3\, V E \sin\delta}{X_s}, \qquad \operatorname{Im} S = \frac{3\, V\,(E\cos\delta - V)}{X_s}.$$

These are the power–angle relations: $\operatorname{Re} S$ and $\operatorname{Im} S$ are the terminal
[real power](real-power.md) and [reactive power](reactive-power.md) delivered to the bus.
Equivalently, in rectangular form, the complex power of this current is
$S = 3 V E \sin\delta / X_s + i\, 3 V (E\cos\delta - V) / X_s$.
