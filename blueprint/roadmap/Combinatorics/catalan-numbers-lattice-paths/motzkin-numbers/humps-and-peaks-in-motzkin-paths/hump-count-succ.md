# Recurrence for hump counts in the path length

A Motzkin path of length $n$ is a word of $n$ steps up ($+1$), flat ($0$) or down ($-1$) that ends at height $0$ and never goes below height $0$; a hump of height $k$ in it is an up step and a later down step with only flat steps between them, where the up step ends at height $k$. Let $H_{n,k}$ be the number of Motzkin paths of length $n$ with one distinguished hump of height $k$, and let $W(n, 0, h)$ be the number of walks of $n$ such steps from height $0$ to height $h$ that never go below height $0$. For natural numbers $n \ge 2$ and $k \ge 1$,

$$H_{n+1,k} = H_{n,k} + W(n, 0, 2k-1).$$
