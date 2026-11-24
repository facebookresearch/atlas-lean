# A common change of cycle unit leaves the Miner damage sum unchanged

For a finite class type, real counts $n_i$, positive lives $N_i > 0$ and a factor $c > 0$,

$$
\sum_i \frac{c\, n_i}{c\, N_i} = \sum_i \frac{n_i}{N_i} \qquad \text{and} \qquad
\sum_i \frac{c\, n_i}{N_i} = c \sum_i \frac{n_i}{N_i}.
$$

Changing the cycle unit of the counts and the lives together (cycles to reversals: $c = 2$) leaves
the [damage sum](miner-damage.md) unchanged, while converting only the counts multiplies it by $c$:
counts in reversals read against lives in cycles double it. The second identity also shows that the
sum scales linearly with a common factor on the counts, with no cap at $D = 1$.

In the physical reading the counts are nonnegative; both identities hold for all real counts.
