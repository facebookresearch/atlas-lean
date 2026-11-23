# Result and cost of the stack operations

Let $\alpha$ be a type, let $s$ be a stack over
$\alpha$ (a list of elements of $\alpha$ whose first element is the top) and let $v \in \alpha$.
Pushing $v$ onto $s$ returns the stack with top $v$ followed by the elements of $s$, at cost $1$.
Popping $s$ returns underflow (no value) at cost $0$ if $s$ is empty, and returns the pair
$(h, t)$ at cost $1$ if $s$ has top $h$ and remaining stack $t$. Reading the top of $s$ returns
underflow (no value) at cost $0$ if $s$ is empty, and returns $h$ at cost $1$ if $s$ has top $h$.
