# Probability Mechanism

A direct mechanism for one seller and one buyer with reports `(s, b)` in `[0,1]²`.
It specifies the probability `x` of trade, the net amount the buyer pays and the net amount
the seller receives. Each amount is real (a negative amount reverses that flow) and is not a
price conditional on trade. As with `BilateralMechanism`, functions are written on real
arguments, but only their restrictions to the unit square describe outcomes.
