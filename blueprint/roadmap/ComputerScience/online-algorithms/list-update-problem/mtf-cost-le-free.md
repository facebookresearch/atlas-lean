# Move-to-front is 2-competitive

In the model of Sleator and Tarjan (1985) with free
exchanges, let $M$ be a list of distinct items and $\sigma$ a sequence of $m$ requests, each an
item of $M$. Consider an offline algorithm given by lists $L_0, L_1, \ldots$, each a
rearrangement of $M$ with $L_0 = M$, and natural numbers $J_0, J_1, \ldots$. It serves request
$t$ (counting from $0$) with the list $L_t$ and pays the position of the request in $L_t$
(counting from $1$). If more than $J_t$ items precede the request in $L_t$, it then moves the
request forward for free so that exactly $J_t$ items precede it, keeping the order of the other
items. Finally it pays one for each pair of items whose relative order differs between the
resulting list and $L_{t+1}$. Then the access cost of move-to-front on $\sigma$ starting from
$M$, plus $m$, is at most twice the total cost of the offline algorithm.
