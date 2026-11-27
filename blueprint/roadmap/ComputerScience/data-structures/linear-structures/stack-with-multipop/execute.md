# Running a sequence of stack operations

Given a stack $S$ and a finite sequence of
operations, each a PUSH of a value, a POP or a MULTIPOP with an integer count, the operations are
applied to $S$ in order. PUSH of $x$ puts $x$ on top at cost $1$; POP removes the top element at
cost $1$; MULTIPOP with count $k$ is MULTIPOP with an integer count, costing one unit per element
removed. If a POP meets an empty stack, the run stops and reports an error, that POP is not
charged, and the cost is that of the operations before it. Otherwise the run returns the final
stack, and its cost is the sum of the costs of all operations.
