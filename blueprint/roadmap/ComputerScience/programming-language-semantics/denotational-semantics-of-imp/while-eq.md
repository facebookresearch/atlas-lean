# The while denotation is a fixed point

Let $b$ be a Boolean expression and $c$ an IMP
command, let $W$ be the relational denotation of $\mathtt{while}\ b\ \mathtt{do}\ c$, and let
$\Phi$ be the one-step unfolding functional of a while loop with guard $b$ and body relation the
denotation of $c$. Then $W = \Phi(W)$.
