# Radiator rate with the temperature clipped to a box

For real `C`, `K_rad`, `Q`, `T_min`, `T_max` and `T`, the clipped radiator rate is the
[radiator rate](radiator-rate.md) at the clipped temperature `min(max(T, T_min), T_max)`. It is
meant for `T_min ≤ T_max`, where the clipped temperature lies in `[T_min, T_max]`; it is defined for
every real `T` and agrees with the radiator rate on the box
([agreement](clipped-radiator-rate-eq-of-mem.md)).
