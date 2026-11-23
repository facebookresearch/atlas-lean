# Inclusive first-hit prefix of a list

Let $p$ be a test that is true or false on each element of a type, and let
$L = [x_1, \dots, x_n]$ be a list. The inclusive first-hit prefix of $L$ for $p$ is
$[x_1, \dots, x_k]$, where $k$ is the least index with $p(x_k)$ true; it includes that first hit.
If $p$ is false on every element of $L$, it is the whole list $L$.
