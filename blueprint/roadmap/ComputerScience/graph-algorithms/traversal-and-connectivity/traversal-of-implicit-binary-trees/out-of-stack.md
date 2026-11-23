# Stack invariants hold for every collected leaf

Let $P$ be a property of states and $s$ a state. Suppose that for every $i \in \mathbb{N}$, every
state on the stack after $i$ depth-first rounds from the pair (stack $[s]$, empty output)
satisfies $P$. Then for every $i$, every state in the output after $i$ rounds from that pair
satisfies $P$.
