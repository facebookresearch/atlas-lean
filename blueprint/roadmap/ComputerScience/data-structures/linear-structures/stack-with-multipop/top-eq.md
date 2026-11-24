# Result and cost of reading the stack top

Let $s$ be a stack over a type $\alpha$ (a list
of elements of $\alpha$ whose first element is the top). If $s$ is empty, reading the top of $s$
returns underflow (no value) at cost $0$. If $s$ has top $h$, reading the top of $s$ returns $h$
at cost $1$.

This holds for every type $\alpha$; no element of $\alpha$ is assumed to exist.
