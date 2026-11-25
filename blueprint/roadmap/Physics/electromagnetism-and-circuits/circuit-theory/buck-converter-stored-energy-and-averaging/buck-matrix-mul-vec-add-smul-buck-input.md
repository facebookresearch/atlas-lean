# The buck state equations in matrix form

For all real `L`, `C`, `R`, `Vin`, `s`, `i` and `v`, the [state matrix](buck-matrix.md) `A` and the
[input vector](buck-input.md) `b` satisfy `A (i, v) + s b = ((s Vin - v) / L, (i - v / R) / C)`: the
right-hand sides of the inductor law `L i' = s Vin - v` and the capacitor law `C v' = i - v / R`.
