# The step through the stability polynomial

One RK4 step of size `dt` of the bath field
multiplies the excess `T - T_amb` by `R(z) = 1 + z + z² / 2 + z³ / 6 + z⁴ / 24` with
`z = (-1 / τ) dt`: `rk4_stability` after the shift.
