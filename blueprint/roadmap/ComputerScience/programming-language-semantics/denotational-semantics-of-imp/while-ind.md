# Park induction for while loops

Let $b$ be a Boolean expression, $c$ an IMP command and
$P$ a binary relation on states, and let $\Phi$ be the one-step unfolding functional of a while
loop with guard $b$ and body relation the denotation of $c$. If $\Phi(P) \subseteq P$, then
for all states $s$ and $s'$ related by the relational denotation of
$\mathtt{while}\ b\ \mathtt{do}\ c$, $P$ relates $s$ to $s'$.
