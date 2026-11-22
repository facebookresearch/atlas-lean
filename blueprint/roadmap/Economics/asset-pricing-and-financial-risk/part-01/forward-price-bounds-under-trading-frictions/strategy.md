# Static trading strategy in spot, cash and forwards

A static trading strategy is five real numbers `(x, y, L, B, f)`: `x` units of the underlying
bought at the ask, `y` units sold short at the bid, cash `L` lent, cash `B` borrowed, and a
long forward position of `f` units (short when `f < 0`). Any real values are allowed here;
admissible strategies also require `x, y, L, B ≥ 0`.
