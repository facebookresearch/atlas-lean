# Valid sparse table

A sparse table over a type with a minimum operation, whose data is a
list $a$ of length $n$, is valid when it has exactly $m + 1$ levels, where
$m = \lfloor \log_2 n \rfloor$ for $n \ge 1$ and $m = 0$ for $n = 0$, and for each $k \le m$ its
level $k$ is the list $L_k$ defined by $L_0 = a$ and, for $x = L_j$, $L_{j+1}$ is the list of
length $|x| - 2^j$ (empty when $2^j \ge |x|$) whose entry $i$ is $\min(x_i, x_{i + 2^j})$. For a
linear order, $L_k$ is the list of minima of the length-$2^k$ slices of $a$.

Tables produced by the construction are valid, an arbitrary value such as data $(1)$ with the
single level $(99)$ is not, and query correctness is stated only for valid tables.
