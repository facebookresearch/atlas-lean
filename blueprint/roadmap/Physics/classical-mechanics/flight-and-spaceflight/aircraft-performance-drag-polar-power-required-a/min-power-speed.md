# Min Power Speed

Minimum-power speed `V_mp = √(√(b / (3 * a)))`. For positive weight and `ρ, S, CD0, k > 0` it
is the unique positive speed of least power required (`levelPower_minPowerSpeed_lt`). As a
formula it is the positive root of `V ^ 4 = b / (3 * a)` whenever `W ≠ 0` and `ρ, S, CD0, k > 0`
(`minPowerSpeed_pos`, `minPowerSpeed_pow_four`). If `CD0 = 0`, `k = 0` or `W = 0`, Lean's
conventions `x / 0 = 0` and `√0 = 0` give the value `0`, which is not a positive speed.
