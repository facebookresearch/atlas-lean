# Generator of the mass-action chain on a finite state class

The generator of the stochastic mass-action chain restricted to a finite set `Ω` of
states: `Q x y = ∑_r λ_r(x) ([fire r x = y] - [x = y])`. It is a rate matrix when `Ω` is
closed under firing (`isRateMatrix_classGenerator`).
