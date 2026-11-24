# Normalized Cocycle

A normalized central (multiplicative) 2-cocycle `c : G → G → A`
with trivial action.

Fields:
- `cocycle g h` is the value `c g h`;
- `one_left : c 1 g = 1`;
- `one_right : c g 1 = 1`;
- `cocycle_assoc : c g h * c (g*h) k = c g (h*k) * c h k`.
