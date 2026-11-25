# Radiator rate with the temperature clipped to a box

For real `C`, `K_rad`, `Q`, `T_min`, `T_max` and `T`, the clipped radiator rate is the
[radiator rate](radiator-rate.md) at the clipped temperature `min(max(T, T_min), T_max)`, the
temperature clipped to the box `[T_min, T_max]`. It is meant for `T_min ≤ T_max` and is defined for
every real `T`; for `T` in `[T_min, T_max]` it equals the radiator rate at `T`
([agreement on the box](clipped-radiator-rate-eq-of-mem.md)). For `T_min > T_max` the clipped
temperature is `T_max` for every `T`, so the clipped rate is the radiator rate at `T_max`.
