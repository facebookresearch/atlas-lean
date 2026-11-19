# Correctness of minimum extraction

Let $c$ be an element of a linearly ordered type and
$L$ a list over it, and let $(m, r)$ be the pair returned by minimum extraction from $L$ with
initial candidate $c$. Then the list $m$ followed by $r$ is a permutation of the list $c$ followed
by $L$, $m \le c$, and $m \le x$ for every element $x$ of $L$.
