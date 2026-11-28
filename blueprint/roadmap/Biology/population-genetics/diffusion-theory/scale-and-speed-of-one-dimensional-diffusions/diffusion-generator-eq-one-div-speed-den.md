# Canonical form of the generator of a regular diffusion

Let `b`, `a` define a
[regular diffusion](../selection-duality-and-general-one-dimensional-di/is-regular-diffusion.md) on
`(0, 1)` (`a` positive and continuous on `(0, 1)`, `b / a` continuous on `(0, 1)` and integrable on
`[0, 1]`; accessibility of the endpoints and a probability normalization are not part of this) and
let `f` be a real function whose derivative `f'` (taken to be `0` where `f` is not differentiable)
is differentiable on `(0, 1)`. Then for every `x ∈ (0, 1)` the
[backward generator](../selection-duality-and-general-one-dimensional-di/diffusion-generator.md) is

`(L_{b,a} f)(x) = (1 / m(x)) (f' / ψ)'(x)`,

where `m` is the [speed density](speed-density.md) and `ψ` the
[scale density](../selection-duality-and-general-one-dimensional-di/scale-density.md): the generator
is `(d/dm)(d/dS)`, with `S` the scale function.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981),
  ch. 15.
