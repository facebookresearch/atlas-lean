# Erdős Problem 1216 is false

It is not the case that $f(n) = \lfloor \log_2 n \rfloor + 1$ for
every $n \ge 1$, where $f(n)$ is the largest $m$ such that every tournament on $n$ vertices
contains a transitive subtournament on $m$ vertices.

Reid and Parker proved $f(n) \ge \lfloor \log_2 n + 4 - \log_2 7 \rfloor$ for all $n \ge 14$; at
$n = 14$ this gives $f(14) \ge 5 > 4 = \lfloor \log_2 14 \rfloor + 1$, while Stearns' bound
$f(n) \ge \lfloor \log_2 n \rfloor + 1$ holds for every $n \ge 1$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1216, https://www.erdosproblems.com/1216 (status DISPROVED); resolution: K. B. Reid and E. T. Parker, Disproof of a conjecture of Erdős and Moser on tournaments, J. Combinatorial Theory 9 (1970), 225-238, erdosproblems.com/1216: f(n) ≥ ⌊log₂ n + 4 - log₂ 7⌋ for all n ≥ 14, so f(14) ≥ 5 > ⌊log₂ 14⌋ + 1.
