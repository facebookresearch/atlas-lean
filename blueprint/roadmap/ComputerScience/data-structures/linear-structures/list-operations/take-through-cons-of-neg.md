# Inclusive first-hit prefix when the head is not a hit

Let $p$ be a test that is true or false on each element, $x$ an element and $L$ a list. If $p(x)$
is false, then the inclusive first-hit prefix for $p$ of the list with head $x$ and tail $L$ is
$x$ followed by the inclusive first-hit prefix of $L$ for $p$.
