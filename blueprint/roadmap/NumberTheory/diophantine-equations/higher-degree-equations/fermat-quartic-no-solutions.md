# No solutions of x⁴ + y⁴ = z² in integers with x and y nonzero

There are no positive integers $x, y, z$ with $x^4 + y^4 = z^2$. Equivalently, Mathlib states that for all integers $a, b, c$ with $a \neq 0$ and $b \neq 0$ one has $a^4 + b^4 \neq c^2$; no condition is imposed on $c$. The two forms are equivalent by passing to absolute values, since $a^4 + b^4 > 0$ excludes $c = 0$.

## Sources

- Kenneth Ireland and Michael Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Graduate Texts in Mathematics 84, Springer-Verlag, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the nonexistence of integers a, b, c with a ≠ 0, b ≠ 0 and a^4 + b^4 = c^2: `not_fermat_42`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/FLT/Four.lean#L256.
