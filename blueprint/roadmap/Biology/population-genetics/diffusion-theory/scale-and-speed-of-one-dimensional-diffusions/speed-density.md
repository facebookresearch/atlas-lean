# Speed density of a one-dimensional diffusion

For real functions `b`, `a` and a real number `x`, the speed density is

`m(x) = 2 / (a(x) ψ(x))`,

where `ψ` is the
[scale density](../selection-duality-and-general-one-dimensional-di/scale-density.md) of drift `b`
and variance `a`; `ψ` is positive everywhere, while `a` is an unrestricted real function. Division
by `0` gives `0`, so `m(x) = 0` wherever `a(x) = 0`; for instance `m(0) = m(1) = 0` when
`a(x) = x (1 - x)`. The intended domain is `x ∈ (0, 1)` for a
[regular diffusion](../selection-duality-and-general-one-dimensional-di/is-regular-diffusion.md),
where `a > 0`: there `m(x)` is [positive](speed-density-pos-of-is-regular.md) and is the speed
density of the diffusion.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981),
  ch. 15.
