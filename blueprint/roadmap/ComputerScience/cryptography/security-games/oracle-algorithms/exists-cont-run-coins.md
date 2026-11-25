# Two-phase bounds on presampled coins

Let $O : X \times R \to Y$ answer a query $x$ with a coin $\rho$ by $O(x, \rho)$. An oracle computation
with queries in $X$ and answers in $Y$ is run on a list of coins by answering its $i$-th query with the
$i$-th coin of the list, and with a fixed default coin once the list is used up. If the computation
satisfies the two-phase query bound with condition $C$ and budget $n$, then for every list of coins
its output $a$ on those coins satisfies $C(a, j)$ for some $j \le n$.
