# Mistake bound for the penalty $1/2$ in integers

Run the weighted majority algorithm
with rational weights and penalty $1/2$ on a list of rounds with $n$ experts, starting from
weight $1$ on every expert, and let $M$ be its number of mistakes. Then every expert $i$, with
$m$ mistakes on these rounds, satisfies $4^M \le n \cdot 3^M \cdot 2^m$ in the natural numbers.

Taking logarithms, $M \le (m + \log_2 n) / \log_2 (4/3) \approx 2.41 (m + \log_2 n)$.
