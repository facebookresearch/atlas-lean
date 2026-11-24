# The ordering check implies interval validity

Let $T$ be an interval tree and let
$\ell$ and $u$ be optional lower and upper key bounds. If the executable check of $T$ with
bounds $\ell$ and $u$, which tests that every key lies strictly between its bounds and that every
stored interval passes the Boolean validity test, returns true, then every interval stored in
$T$ is valid, that is, its low endpoint is at most its high endpoint.
