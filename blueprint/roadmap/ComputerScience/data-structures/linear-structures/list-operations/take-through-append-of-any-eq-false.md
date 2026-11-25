# Inclusive first-hit prefix of an append with no hit on the left

Let $p$ be a test that is true or false on each element, and let $L$ and $M$ be lists. If $p$ is
false on every element of $L$, then the inclusive first-hit prefix for $p$ of the concatenation
$L$ followed by $M$ is $L$ followed by the inclusive first-hit prefix of $M$ for $p$.
