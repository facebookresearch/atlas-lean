# Pointwise decay of the quadratic energy about a reference value

Let `C > 0`, let `T*` be any reference value, and let `T` be differentiable at a time `t` with
`C T'(t) = F(T(t))`, that is `T'(t) = F(T(t)) / C`. If `(T(t) - T*) F(T(t)) < 0`, then the
energy `V(s) = (T(s) - T*)² / 2` is differentiable at `t` with
`V'(t) = (T(t) - T*) F(T(t)) / C < 0`.

`T*` need not be an equilibrium and no sign condition is assumed near `T*`, so this alone says
nothing about attraction. At an equilibrium (`F(T*) = 0`) where `F` is differentiable on a
neighbourhood of `T*` and `F' < 0` there except possibly at `T*`, so that `(T - T*) F(T) < 0` there
by [the restoring sign](local-sign.md), it gives the Lyapunov reading: `V' < 0` at every time the
solution lies in that neighbourhood but not at `T*`.
