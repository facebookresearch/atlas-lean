# Carry insertion into a binomial forest

For a linearly ordered type, the carry of a
binomial tree $t$ into a list $F$ of binomial trees is defined by recursion on $F$. If $F$ is
empty, the result is the one-tree list $[t]$. If $F$ starts with a tree $u$ followed by a list
$F'$ and the rank of $t$ is less than the rank of $u$, the result is $F$ with $t$ prepended.
Otherwise the result is the carry of the link of $t$ and $u$ into $F'$.

It is meant for a tree whose rank is no greater than every rank in the forest, where linking
equal-rank trees propagates like a binary carry.
