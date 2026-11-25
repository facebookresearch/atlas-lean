# The adversary makes every access cost the full length of the list

Let $M$ be a nonempty
list of $\ell$ distinct items and let $A$ be a deterministic online list-update algorithm on the
items of $M$. For every default item $d$, every natural number $n$ and every state $q$ of $A$,
the cost of $A$ from state $q$ on the adversary's sequence of $n$ requests from $q$ with default
item $d$ is $n \ell$.
