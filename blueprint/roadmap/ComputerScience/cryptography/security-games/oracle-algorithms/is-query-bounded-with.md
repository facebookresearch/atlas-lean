# Two-phase query bound

Let $C$ be a condition on an output and a natural number, the budget left for a second phase. An
oracle computation $c$ satisfies the two-phase query bound with condition $C$ and budget $q$ when,
along every path, whatever the answers, it asks some number $j \le q$ of queries and its output
$x$ satisfies $C(x, q - j)$.
