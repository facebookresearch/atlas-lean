# Aggregating cycle records by class preserves total count and damage

Let the record type $\kappa$ and the class type $\iota$ be finite, let each record $k$ carry a count
$r_k \ge 0$ and a class $g(k)$, and let every class have a life $N_i > 0$. The
[class counts](cycle-class-counts.md) $n_i = \sum_{k : g(k) = i} r_k$ then satisfy:

- $n_i \ge 0$ for every class $i$;
- $\sum_i n_i = \sum_k r_k$: aggregation conserves the total count;
- $\sum_i n_i / N_i = \sum_k r_k / N_{g(k)}$: the [damage sum](miner-damage.md) of the class counts
  equals the record-wise sum, in which each record is read as a class of its own with the life of
  its class.

So reordering or regrouping records, and merging or splitting classes of equal life, leave the
damage sum unchanged.
