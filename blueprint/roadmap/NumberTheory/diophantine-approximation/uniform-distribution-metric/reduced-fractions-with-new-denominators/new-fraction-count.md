# Fractions with a new denominator

For a sequence $n_0, n_1, \dots$ of natural numbers and a natural number $k$, $\varphi_A(k)$ is the number of $m \in \{1, \dots, n_k\}$ such that $n_k/\gcd(m, n_k)$ divides no $n_j$ with $j < k$. For positive terms this counts the fractions $m/n_k$ that cannot be written with denominator $n_j$ for any $j < k$: the reduced denominator $n_k/\gcd(m, n_k)$ divides none of the earlier terms. If $n_k = 0$ the range is empty and the count is $0$; if some earlier $n_j$ is $0$, every candidate divides it, so this count, and every later one, is $0$.
