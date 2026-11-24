# Solution built by the method of steps

For real numbers `r`, `K` and `τ` and a history `φ`, the method-of-steps solution at `t` is the
value at `t` of the `⌈t / τ⌉₊`-th [iterate](step-iter.md) of the [step map](step-map.md), started at
the [extended history](history-ext.md) of `φ`, where `⌈·⌉₊` is the natural ceiling (`0` for negative
arguments). It is defined for every `τ`; for `τ = 0`, where `t / 0 = 0`, it is the extended history,
which is then the constant `φ(0)`. The intended domain is `τ > 0`, where it
[solves the equation](is-solution-solution.md) for a continuous history.
