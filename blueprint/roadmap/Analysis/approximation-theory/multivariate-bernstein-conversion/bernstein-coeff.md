# Bernstein Coeff

For finitely many variables, the Bernstein coefficient of a real polynomial `p` at index `k`
and coordinate degrees `n`: sum over the power-basis support of `p`, multiplying
each coefficient by `∏ i, choose (k i) (d i) / choose (n i) (d i)`.
A ratio with zero denominator is zero, by the convention for real division.
Reconstruction requires `p.degreeOf i ≤ n i` for every coordinate.
