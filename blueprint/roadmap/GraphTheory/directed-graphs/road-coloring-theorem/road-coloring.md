# Road coloring theorem for a finite vertex type

Let $V$ be a finite nonempty set and let
$\to$ be a relation on $V$, viewed as a directed graph on $V$ without parallel edges (loops
allowed). Suppose that the graph is strongly connected (for all $u, v \in V$ there is a directed
walk, possibly of length $0$, from $u$ to $v$), aperiodic (for every integer $d > 1$ there is a
closed directed walk of positive length not divisible by $d$), and of constant positive
out-degree (there is $k > 0$ such that every vertex has exactly $k$ out-neighbours). Then there
exist a natural number $\ell$ and a map $\delta : V \times \{0, \dots, \ell - 1\} \to V$ such that
for every $v \in V$ the map $c \mapsto \delta(v, c)$ is a bijection from $\{0, \dots, \ell - 1\}$
onto the out-neighbours of $v$, together with a word $c_1 \cdots c_m$ over $\{0, \dots, \ell - 1\}$
and a vertex $r$ such that following the labels $c_1, \dots, c_m$ in order from any vertex $v$
ends at $r$.

This form only assumes that $V$ is finite, as a property, rather than being given a finite set of
all its elements as data.
