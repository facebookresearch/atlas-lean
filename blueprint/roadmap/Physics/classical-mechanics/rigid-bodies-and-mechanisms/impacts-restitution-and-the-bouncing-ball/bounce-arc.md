# For positive m and g, each active arc is a ballistic flight

Let `m > 0`, `g > 0`, `e` and `u₀` real, and let arc `n` be [active](is-active-arc.md): its
[take-off speed](bounce-speed.md) `u_n` is positive. Consider the
[constant-force trajectory](../../particles-and-oscillations/kinetic-energy-and-power-of-a-force/const-force-position.md)
of a body of mass `m` leaving the floor (height `0`) with upward velocity `u_n` under its weight
`-m g`: height `x(t) = t u_n - g t² / 2` and velocity `u_n - g t`. Then, with the
[flight duration](flight-duration.md) `T_n = 2 u_n / g`:

- `T_n > 0`;
- `x(T_n) = 0`, and `x(t) > 0` for `0 < t < T_n`;
- the landing velocity is `-u_n`;
- the fixed-wall event applied to the landing velocity gives `-e (-u_n) = u_(n+1)`, the take-off
  speed of the next arc.

For `e > 0` and `u₀ > 0` every arc is active ([all arcs active](is-active-arc-of-pos.md)); for
`e = 0` and `u₀ > 0` only the first one is ([termination](inelastic-stops.md)).
