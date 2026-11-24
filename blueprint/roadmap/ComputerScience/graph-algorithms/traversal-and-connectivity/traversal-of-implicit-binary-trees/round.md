# One depth-first round of binary branching

For a branching step on states, one depth-first round acts on a pair (stack, output) of lists of
states. If the stack is empty, the pair is unchanged. If the stack has top $s$ and rest $R$: when
$s$ is terminal, the result is the stack $R$ with $s$ placed in front of the output; when $s$
branches into $(l, h)$, the result is the stack $l, h$ followed by $R$, with the output unchanged.
