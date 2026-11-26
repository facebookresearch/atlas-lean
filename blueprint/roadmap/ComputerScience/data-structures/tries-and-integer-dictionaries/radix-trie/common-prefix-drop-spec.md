# Longest common prefix in terms of dropped remainders

Let $s$ and $t$ be lists over a type
with decidable equality, let $p$ be their longest common prefix, of length $n$, and let $s'$ and
$t'$ be the lists obtained from $s$ and $t$ by dropping their first $n$ elements. Then $s$ is $p$
followed by $s'$, $t$ is $p$ followed by $t'$, and either $s'$ is empty, or $t'$ is empty, or
$s'$ and $t'$ are both nonempty with different first elements.
