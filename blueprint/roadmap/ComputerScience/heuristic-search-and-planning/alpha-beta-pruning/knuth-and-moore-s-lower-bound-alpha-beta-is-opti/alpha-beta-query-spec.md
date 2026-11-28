# The alpha-beta query algorithm agrees with alpha-beta

For every leaf valuation $f$, side to move, window $(a, b)$ and shape $s$, the alpha-beta query
algorithm returns the value that alpha-beta computes on the tree obtained by instantiating $s$ with
$f$, and makes exactly one query per leaf that alpha-beta evaluates there.
