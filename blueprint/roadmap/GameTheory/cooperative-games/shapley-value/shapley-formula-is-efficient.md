# Shapley's formula is efficient

Shapley's formula distributes exactly the worth of the grand coalition:
$\sum_{i \in N} \varphi_i(v) = v(N)$.

Regrouping the double sum by coalitions, $v(T)$ appears with coefficient $|T|\,w(n, |T|)$ from
the players of $T$ and with coefficient $-(n - |T|)\,w(n, |T| + 1)$ from the coalitions
$T \cup \{j\}$, $j \notin T$. By the telescoping identity only $T = N$ survives, with coefficient
$1$; the empty coalition contributes nothing since $v(\emptyset) = 0$.

## Informally uses

- [Telescoping of the Shapley weights](shapley-weight-telescope.md): the cancellation of the
  coefficients.

## Background

- [Efficient value](is-efficient.md): the property proved.
