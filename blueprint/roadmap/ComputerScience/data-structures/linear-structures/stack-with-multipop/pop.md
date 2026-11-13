# Stack pop

Stacks over a type $\alpha$ are lists of elements of $\alpha$, with the first
element as the top. Popping the empty stack returns underflow (no value) at cost $0$. Popping a
stack with top $v$ and remaining stack $t$ returns the pair $(v, t)$ at cost $1$ (one successful
pop event).
