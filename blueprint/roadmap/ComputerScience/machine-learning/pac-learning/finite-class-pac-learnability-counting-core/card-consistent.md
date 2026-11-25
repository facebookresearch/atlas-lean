# Card consistent

Assume that equality on `X` is decidable and that `X` is finite.

A hypothesis `h` is consistent with the target `c` on a sample `s : Fin m → X` when it
agrees with `c` at every sampled point. The number of such samples is `a ^ m`, where `a` is the
number of points at which `h` and `c` agree.
