# Littlestone–Warmuth mistake bound

Let $K$ be a linearly ordered field and let
$\beta \in K$ with $0 \le \beta \le 1$. Run the weighted majority algorithm with penalty $\beta$
on a list of rounds with $n$ experts, starting from weight $1$ on every expert, and let $M$ be its
number of mistakes. Then every expert $i$, with $m$ mistakes on these rounds, satisfies
$\beta^m 2^M \le n (1 + \beta)^M$.
