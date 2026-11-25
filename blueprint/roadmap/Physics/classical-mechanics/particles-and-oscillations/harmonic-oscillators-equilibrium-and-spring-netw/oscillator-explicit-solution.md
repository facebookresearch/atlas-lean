# For m, k > 0, A cos(ωt) solves the oscillator with energy k A² / 2

Let `m > 0` and `k > 0`, let `ω = √(k / m)`, and let `A` and `t` be real numbers. Then, at the
time `t`:

- `s ↦ A cos (ω s)` has derivative `-A ω sin (ω t)`;
- `s ↦ -A ω sin (ω s)` has derivative `-(k / m) A cos (ω t)`;
- the [oscillator energy](oscillator-energy.md) of the position `A cos (ω t)` and velocity
  `-A ω sin (ω t)` is `(1/2) k A²`.

So `x(s) = A cos (ω s)` and `v(s) = -A ω sin (ω s)` solve `x' = v`, `v' = -(k / m) x` at every time,
with the same energy `(1/2) k A²` at every time.
