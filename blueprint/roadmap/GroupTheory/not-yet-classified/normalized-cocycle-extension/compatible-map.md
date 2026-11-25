# Compatible Map

Compatible map between normalized cocycles.

Data:
- `f : G →* G'` (base hom);
- `g : A →* A'` (coefficient hom);
- `q : G → A'` with `q 1 = 1`;
- `compat : g (c x y) * q (x*y) = q x * q y * d (f x) (f y)`.

Induced map is `(x,a) ↦ (f x, g a * q x)`.
