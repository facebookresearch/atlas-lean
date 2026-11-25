# Functional calibrated on bending–torsion states with a shear factor

Let $\Phi$ be a real function on $3 \times 3$ real stress matrices (tension positive), for example a
yield functional, and $c$ a real number. Then $\Phi$ is calibrated on the bending–torsion states
with shear factor $c$ when

- $c > 0$, and
- for all real $\sigma$ and $\tau$, $\Phi$ takes the value $\sqrt{\sigma^2 + c \tau^2}$ on the
  [bending–torsion state](bending-torsion-state.md) $S(\sigma, \tau)$.

In the physical reading, $c = 3$ is the shear factor of the von Mises (distortion-energy) criterion
and $c = 4$ that of the Tresca (maximum-shear) criterion. The factor must be positive: for $c \le 0$
a pure torque ($\sigma = 0$) would get the value $\sqrt{c \tau^2} = 0$, the square root of a
negative number being taken as $0$.