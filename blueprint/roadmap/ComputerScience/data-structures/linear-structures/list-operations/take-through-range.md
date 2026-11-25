# Inclusive first-hit prefix of a range of naturals

Let $q$ be a test that is true or false on each natural number, and let $n$ be a natural number.
The inclusive first-hit prefix for $q$ of the list $[0, 1, \dots, n-1]$ is the list
$[0, 1, \dots, m-1]$, where $m = i + 1$ if $i$ is the least number below $n$ with $q(i)$ true,
and $m = n$ if $q$ is false on every number below $n$.
