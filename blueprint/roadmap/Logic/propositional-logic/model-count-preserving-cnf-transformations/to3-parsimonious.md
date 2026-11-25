# Parsimonious reduction of CNF to 3-CNF

For a CNF formula $\varphi$ and a natural number `start`, every clause with more than three
literals is split into clauses with at most three. Each step replaces the first two literals
$\ell_1, \ell_2$ of a long clause by a new variable $y$ and adds the clauses
$\neg y \lor \ell_1 \lor \ell_2$, $y \lor \neg\ell_1$ and $y \lor \neg\ell_2$, which force $y$ to
equal $\ell_1 \lor \ell_2$. The new variables are `start`, `start + 1`, …, one for each literal
beyond the third in each clause. Repeated output clauses are then removed, keeping last
occurrences.

The function is defined for every `start`; the new variables are guaranteed to be fresh provided
that every variable of $\varphi$ is below `start`, which the model-count and unique-extension
theorems assume. Otherwise
the reduction can change the set of models: for $\varphi = x_0 \lor x_1 \lor x_2 \lor x_3$ and
`start` $= 0$, the new variable is $x_0$ itself and the output forces $x_1 \to x_0$.
