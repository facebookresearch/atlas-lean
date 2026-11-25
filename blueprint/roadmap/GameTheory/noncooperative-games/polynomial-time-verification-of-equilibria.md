# Polynomial-time verification of (approximate) equilibria

Given an explicit finite game with rational payoffs, a rational mixed profile $\sigma$ (each $\sigma_i$ a probability vector) and, for the
approximate version, a rational $\varepsilon \ge 0$, deciding whether $\sigma$ is a Nash equilibrium, or an $\varepsilon$-Nash equilibrium (no player gains more than
$\varepsilon$ by a unilateral pure deviation), takes time polynomial in the total bit size of the payoff table and of $\sigma$: compute each player's
expected payoff and the payoff of each pure deviation, and compare. For succinct games the bound needs an expectation oracle and is a
separate statement. In operation counts, for $n$ players with strategy sets $S_1, \dots, S_n$ of sizes $|S_j| \ge 2$: computing the products $\prod_{j \ne i} \sigma_j(s_j)$ by sharing
prefixes while enumerating the opponents' profiles in lexicographic order, the procedure uses $O(n \prod_j |S_j|)$ additions,
multiplications and comparisons of rationals, hence $O(\sum_i |S_i| \prod_j |S_j|)$; computing each product separately uses
$\Theta(n^2 \prod_j |S_j|)$, which exceeds $\sum_i |S_i| \prod_j |S_j|$ by a factor of order $n$ when all strategy sets have size $2$. These
count operations, not bit operations; the polynomial bound above accounts for the sizes of the rationals.

## Depends on

- [Explicit encoding and size of finite games](explicit-encoding-and-size-of-finite-games.md)
- [Expected payoff of a mixed profile](nash-s-theorem/expected-payoff.md)
- [Mixed Nash equilibrium](nash-s-theorem/is-mixed-nash.md)

## Proof depends on

- [Best-response (support) condition](best-response-condition.md)

## Sources

- CS364A Lecture #20: Mixed Nash Equilibria and PPAD-Completeness — Tim Roughgarden, Stanford University (2013), Section 2 (for bimatrix games it is enough to check pure-strategy deviations). <https://theory.stanford.edu/~tim/f13/l/l20.pdf>
