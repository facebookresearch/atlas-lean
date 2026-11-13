# Frobenius partitions with at most $k$ repetitions

For natural numbers $k$ and $n$,
$\varphi_k(n)$ is the number of generalized Frobenius partitions of $n$ in which each integer
appears at most $k$ times in each row. Concretely, $\varphi_k(n)$ is the number of pairs of
functions $m_1, m_2 \colon \{0, 1, \dots, n\} \to \{0, 1, \dots, k\}$ with
$\sum_i m_1(i) = \sum_i m_2(i)$ and $\sum_i (i + 1)\, m_1(i) + \sum_i i\, m_2(i) = n$.

Here a generalized Frobenius partition of $n$ is a two-rowed array of nonnegative integers with
$r$ columns, both rows nonincreasing, whose entries sum to $n - r$; its entries are at most $n$,
and $m_1(i)$, $m_2(i)$ count how often $i$ appears in the top and bottom rows.

## Sources

- Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4 Repetitions*, INTEGERS 25 (2025), Article A17, Section 1 (definition of `φ_k(n)`, after Andrews).
