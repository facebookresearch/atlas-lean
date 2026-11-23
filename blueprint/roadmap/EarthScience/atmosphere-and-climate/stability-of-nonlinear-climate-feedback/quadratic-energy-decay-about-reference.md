# Quadratic energy decay about reference

Pointwise quadratic-energy decay about an arbitrary reference value
`Tstar`: if `T` solves `C * T' = F(T)` at time `t` (stated as
`HasDerivAt T (F(T t)/C) t`) and `(T t - Tstar) * F(T t) < 0`, then the
energy `V(s) = (T s - Tstar)^2 / 2` has derivative
`(T t - Tstar) * F(T t) / C < 0` at `t`.

`Tstar` need not be an equilibrium and no neighbourhood sign condition is
assumed, so this alone says nothing about attraction. At an equilibrium
(`F Tstar = 0`) where `local_sign` supplies the sign hypothesis, it gives
the Lyapunov reading: `V` decreases at every time the solution lies in the
punctured neighbourhood.
