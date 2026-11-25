# The TE10 mode of a rectangular waveguide filled with a homogeneous medium

Let a waveguide with cross-section $[0, a] \times [0, b]$, $a, b > 0$, be filled with a lossless homogeneous medium of permittivity
$\epsilon > 0$ and permeability $\mu > 0$. For $E_0 \ne 0$, $\omega > 0$ and real $\beta$, define on
$[0, a] \times [0, b] \times \mathbb R \times \mathbb R$

$$E = \Big(0,\ E_0 \sin\frac{\pi x}{a} \sin(\omega t - \beta z),\ 0\Big), \qquad
H = \Big(-\frac{\beta E_0}{\omega\mu} \sin\frac{\pi x}{a} \sin(\omega t - \beta z),\ 0,\
\frac{\pi E_0}{\omega\mu a} \cos\frac{\pi x}{a} \cos(\omega t - \beta z)\Big).$$

Then $(E, H)$ solves the [source-free Maxwell equations](maxwell-equations-in-a-homogeneous-linear-medium.md) of the medium with
$\sigma = 0$, and $E$ and $B = \mu H$ satisfy the perfect-conductor conditions
on the four side walls (the tangential electric field and the normal magnetic field vanish on $x \in \{0, a\}$ and on $y \in \{0, b\}$), if and only if

$$\beta^2 = \omega^2 \epsilon\mu - \Big(\frac{\pi}{a}\Big)^2 .$$

So a real propagation constant exists exactly when $\omega \ge \pi / (a\sqrt{\epsilon\mu})$, the cutoff of the mode. The divergence
equations, Faraday's law and the wall conditions hold for every $\beta$; the $y$-component of Ampère's law holds exactly when
$\beta^2 + (\pi/a)^2 = \omega^2\epsilon\mu$.

## Depends on

- [Maxwell's equations in a homogeneous linear medium](maxwell-equations-in-a-homogeneous-linear-medium.md)

## Sources

- J. D. Jackson, *Classical Electrodynamics*, 3rd edition, Wiley, 1999, Section 8.1 (fields at the surface of a good conductor) and Section 8.4 (modes in a rectangular waveguide).
- D. M. Pozar, *Microwave Engineering*, 4th edition, Wiley, 2012, Section 3.3 (rectangular waveguide).
