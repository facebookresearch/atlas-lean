# The codes of the negative parts follow the golden rotation

Let $n \ge 1$, write $\varphi$
for the golden ratio, $F_k$ for the Fibonacci numbers and $L_k$ for the Lucas numbers, and let
$c$ be a function from the natural numbers to the natural numbers such that
$c(N) = \sum_{i \in S,\, i < 0} F_{i+2n}$ (with $F_k$ read as $0$ for $k < 0$) whenever $S$ is a
base phi expansion of $N$. List the values $c(N)$ for $N = L_{2n-1} + 1, \dots, L_{2n+1}$ (the
interval $\Xi_n$) in increasing order of $N$, and merge every run of equal consecutive values
into a single entry. The resulting list is a permutation of $0, 1, \dots, F_{2n} - 1$, and the
fractional parts $\{(k+1)\varphi\}$ of its entries $k$ strictly decrease along it: if $k$ comes
before $k'$, then $\{(k'+1)\varphi\} < \{(k+1)\varphi\}$.

This list is the paper's permutation $\Pi^\beta_{2n}$ (the codes $C(N)$ of the negative parts
$\beta^-(N)$, tridents merged, as in Theorem 11), and the statement says it is the order in
which the first $F_{2n}$ iterates of the rotation $z \mapsto \exp(2\pi i(z - \varphi))$ occur on
the circle, the entry $k$ standing for the iterate number $k + 1$. This is the reading fixed by
the paper's worked case $n = 3$, where $\Pi^\beta_6 = 7\,2\,5\,0\,3\,6\,1\,4$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 12 (`integers-2024-A24-thm-12`).
