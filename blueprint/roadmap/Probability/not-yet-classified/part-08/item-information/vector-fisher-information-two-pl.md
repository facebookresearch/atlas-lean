# Test information of the two-parameter logistic model

For a finite (possibly empty) item type `ι`, arbitrary real
discriminations `a` and difficulties `b`, and scalar ability `θ`, write
`p j = Real.sigmoid (a j * (θ - b j))`.  The quadratic form at `1` of the vector Fisher information operator of the 2PL density (counting measure on response patterns, density the product mass function, scalar parameter space `ℝ`) satisfies:

1. it is the finite test information `∑ j, (a j)^2 * p j * (1 - p j)`;
2. it is the scalar Fisher information of the same density family at `θ`;
3. the sum is nonnegative, with no further hypothesis;
4. the sum is strictly positive whenever some discrimination is nonzero.

No slope sign, slope nonvanishing or nonemptiness hypothesis is needed: conclusions 1–3 hold also for the empty test (both sides `0`) and for zero slopes, and conclusion 4 is sharp, since a test whose discriminations all vanish has information `0`.
