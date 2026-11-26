# Number of Motzkin walks between two heights

For natural numbers $n$, $a$ and $b$, the number $W(n, a, b)$ is defined by recursion on $n$: $W(0, a, b) = 1$ if $a = b$ and $0$ otherwise; $W(n+1, a, 0) = W(n, a, 0) + W(n, a, 1)$; and $W(n+1, a, b+1) = W(n, a, b) + W(n, a, b+1) + W(n, a, b+2)$. Thus $W(n, a, b)$ counts the walks of $n$ steps up ($+1$), flat ($0$) or down ($-1$) that start at height $a$, end at height $b$ and never go below height $0$.
