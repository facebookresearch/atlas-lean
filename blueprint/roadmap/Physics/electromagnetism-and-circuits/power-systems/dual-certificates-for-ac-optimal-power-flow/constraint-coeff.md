# Constraint Coeff

Coefficient matrix of each inequality of the relaxation, written as
`Re (trace (A * W)) ≤ b`. For bus `k` the six groups are: upper active limit, lower active
limit, upper reactive limit, lower reactive limit, upper squared voltage limit, lower
squared voltage limit; then one squared current limit per branch.
