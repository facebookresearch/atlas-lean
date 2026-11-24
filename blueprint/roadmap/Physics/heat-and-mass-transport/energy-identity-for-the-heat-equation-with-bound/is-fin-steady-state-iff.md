# The fin equations are the steady cable equations

For all real `k`, `A`, `h`, `P`, `Ta`, `L` and functions `T`, `q`, the pair `(T, q)` is a
[steady fin](is-fin-steady-state.md) on `[0, L]` if and only if `θ(x) = T(x) - Ta` and `q` satisfy
the steady cable equations on `[0, L]`, with derivatives within `[0, L]`,

`θ′ = -ri q` and `q′ = -θ/rm`, with `ri = 1/(kA)` and `rm = 1/(hP)`.

The excess temperature plays the voltage and the heat rate the axial current.
