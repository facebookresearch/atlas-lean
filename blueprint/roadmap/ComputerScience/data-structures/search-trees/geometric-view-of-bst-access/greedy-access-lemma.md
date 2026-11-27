# Greedy satisfies the access lemma

Fix positive weights $w(1), \dots, w(n)$ with $W = \sum_a w(a)$. In Fox's potential for geometric Greedy, the amortized cost of the access at time $t$ (one plus the number of points Greedy adds in row $t$, plus the change in potential) is at most $5 + 6\lfloor \log_2 W \rfloor - 6\,r(x_t, t-1)$, where $r(x_t, t-1) \ge \lfloor \log_2 w(x_t) \rfloor$; so the total cost of Greedy on an access sequence $X$ of length $m$ is $O\big(m + \sum_{t=1}^m \log \frac{W}{w(x_t)}\big)$ plus the potential drop $\Phi(0) - \Phi(m)$. The drop depends on the sequence, but since every key's neighborhood contains the key itself, each rank lies between $\lfloor \log_2 w(a) \rfloor$ and $\lfloor \log_2 W \rfloor$, so the drop is at most $\sum_a \big(\lfloor \log_2 W \rfloor - \lfloor \log_2 w(a) \rfloor\big)$, a bound depending only on $n$ and the weights. Consequently Greedy has total cost $O((m + n)\log n)$, and, if every key is accessed at least once and key $a$ is accessed $f(a)$ times, total cost $O\big(m + \sum_a f(a) \log \frac{m}{f(a)}\big)$, the static optimality bound.

## Proof sketch

Fox defines, for each key $x$ at time $t$, a neighborhood $\Gamma(x, t)$: the keys whose access at time $t+1$ would make Greedy touch $x$, an analogue of the subtree of $x$ in the tree view. The size of $x$ is the total weight of its neighborhood, its rank is $\lfloor \log_2 \text{size} \rfloor$, and the potential is the sum of ranks. Keys not touched at time $t$ keep their neighborhoods and hence their ranks, so the amortized cost is a sum over the touched keys. On each side of $x_t$ this sum telescopes except for one unit per touched key of a special kind that Fox calls *stubborn*, and he bounds the number of stubborn keys by $1 + 2\lfloor \log_2 W \rfloor - 2r(x_t, t-1)$, mirroring Sleator and Tarjan's access lemma for splay trees; balance and static optimality follow with uniform weights and with weights $f(a)/m$.

## Depends on

- [Geometric Greedy (Greedy Future)](geometric-greedy.md)

## Sources

- Kyle Fox, "Upper Bounds for Maximally Greedy Binary Search Trees", WADS (2011), arXiv:1102.4884.
