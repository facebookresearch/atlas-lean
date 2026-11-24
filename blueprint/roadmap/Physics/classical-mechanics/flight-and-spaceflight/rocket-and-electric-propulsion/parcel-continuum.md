# Parcel continuum

A differentiable mass history `M` that is burning at `t`, `M' = m' < 0`. A forward parcel step
from `t` to `t + h`, `h > 0`, expels the actual mass `M t - M (t + h)`, at the rate
`q_h = (M t - M (t + h)) / h`, which tends to `-m'`. For small `h > 0` the expelled mass is
nonnegative, the remaining mass `M t - q_h h` is exactly `M (t + h)` and positive, and the step
conserves momentum; its slope at the state `(M t, v)` tends to `(F - ve m') / M t`: the
acceleration `a` of the reduced law `M a = -ve M' + F`.
