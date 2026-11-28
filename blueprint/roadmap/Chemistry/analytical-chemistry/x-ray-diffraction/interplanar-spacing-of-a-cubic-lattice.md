# Interplanar spacing of a cubic lattice

Let $a>0$ and let $(h,k,l)\in\mathbb Z^3\setminus\{(0,0,0)\}$. For the parallel plane family
$P_m=\{(x,y,z):hx+ky+lz=ma\}$, $m\in\mathbb Z$, the distance from $P_m$ to $P_{m+1}$ is
$d=a/\sqrt{h^2+k^2+l^2}$. For the simple cubic point lattice $a\mathbb Z^3$, these are adjacent occupied lattice planes when
$\gcd(|h|,|k|,|l|)=1$. Without this primitive-index condition, some $P_m$ contain no lattice points; for example $(2,0,0)$ gives
planes spaced $a/2$, whereas adjacent occupied planes of $a\mathbb Z^3$ with that normal are spaced $a$. Both $a$ and $d$ are lengths. Bragg's condition for diffraction is a separate physical law, not a consequence of the lattice geometry, and noncubic metrics
are outside this result.

The distance is a minimum over all pairs of real points from the two planes, attained by a
pair displaced along the normal. In fractional coordinates $(x/a,y/a,z/a)$, the plane $P_m$
is the level $m$ of the linear form with coefficients $(h,k,l)$. Occupancy is a separate condition:
a level $m$ is occupied exactly when $\gcd(|h|,|k|,|l|)$ divides $m$ in $\mathbb{Z}$.

## Sources

- MIT OpenCourseWare 3.091, *Introduction to Solid-State Chemistry*, fall 2018, Recitation 14, §2, <https://ocw.mit.edu/courses/3-091-introduction-to-solid-state-chemistry-fall-2018/> (cubic spacing formula).

Bézout's identity gives the occupancy criterion: an integer level is occupied exactly when
the gcd of the indices divides it. For $(2,0,0)$ this means precisely the even levels.
The plane $2x=2ma$ is the same as $x=ma$, so level $2m$ for $(2,0,0)$ is level $m$ for
$(1,0,0)$. Consecutive occupied planes thus correspond to levels $m$ and $m+1$ for
$(1,0,0)$, and the geometric spacing formula gives distance $a$.
