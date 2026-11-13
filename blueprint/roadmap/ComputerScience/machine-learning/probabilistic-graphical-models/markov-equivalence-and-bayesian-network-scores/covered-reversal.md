# Covered-edge reversal

`Pa'` is obtained from `Pa` by reversing a covered edge `x → y` (Chickering 1995): `x` is a
parent of `y` and `y`'s other parents are exactly `x`'s parents (`Pa y = insert x (Pa x)`);
after the reversal `y` has parents `Pa x` and `x` has parents `insert y (Pa x)`. Acyclicity
is not required: the score identity holds for any parent-set maps (on a DAG, `x ∉ Pa x` and
`y ∉ Pa x` hold automatically).
