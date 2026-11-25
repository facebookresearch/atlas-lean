# With a zero life, the bare cycle-ratio sum ignores that class's count

For a finite class type, arbitrary real counts $n_i$ and lives $N_i$, a class $j$ with $N_j = 0$ and
any real $x$, let $n'$ be the counts $n$ with $n_j$ replaced by $x$. Then

$$\sum_i \frac{n'_i}{N_i} = \sum_i \frac{n_i}{N_i}.$$

This is the convention $x / 0 = 0$: the term of class $j$ is $0$ whatever its count, so the bare sum
registers no damage there, although a vanishing life would mean immediate failure. The
[damage sum](miner-damage.md) is defined only for positive lives, so this case does not arise in it.
