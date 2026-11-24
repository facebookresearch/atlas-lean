# One-state linear system of the stirred-tank deviation dynamics

For real numbers $V$ (volume), $Q$ (volumetric flow), $k$ (rate constant) and $C$ (output gain), the
stirred-tank linear system is the one-state
[single-input single-output linear system](../../../Analysis/control-theory/linear-system.md) with

$$A = -\Big(\frac{Q}{V} + k\Big), \qquad b = \frac{Q}{V}, \qquad c = C, \qquad d = 0,$$

so that $\dot x = A x + b u$ and $y = C x$, with no direct feedthrough. In the physical reading
$V > 0$, $Q > 0$ and $k \ge 0$, the state $x$ is the deviation of the concentration from a steady
state and the input $u$ the deviation of the inlet concentration. The definition takes all real
inputs; with the convention $a/0 = 0$, $V = 0$ gives $A = -k$ and $b = 0$.
