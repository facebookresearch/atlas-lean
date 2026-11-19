# Weight-counting depth-first round

For a branching step on states and a weight $w$ from states to natural numbers, one
weight-counting round acts on a pair (stack, count) of a list of states and a natural number. If
the stack is empty, the pair is unchanged. If the stack has top $s$ and rest $R$: when $s$ is
terminal, the result is $(R, c + w(s))$; when $s$ branches into $(l, h)$, the result is the stack
$l, h$ followed by $R$, with the count unchanged.
