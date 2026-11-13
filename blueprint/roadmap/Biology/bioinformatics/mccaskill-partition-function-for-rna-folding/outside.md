# Outside recursion

**Outside recursion** (McCaskill 1990) over a commutative semiring `R`, for a sequence of
length `n = s.length`: `outside pair m s w i j` is the weighted sum of the parts outside the
pair `(i, j)` of all structures containing it (proved in `outside_mul_eq_sum`). Either no pair
encloses `(i, j)`, leaving independent structures on `[0, i)` and `[j + 1, n)`, or there is a
unique innermost enclosing pair `(a, b)` (`a < i`, `j < b < n`), contributing the outside value
of `(a, b)`, its weight, and the inside values of `[a + 1, i)` and `[j + 1, b)`.
