# Basic properties of the convergents of a Laurent series

Let $K$ be a field and let
$\alpha \in K((x^{-1}))$ be irrational, with partial quotients $b_0, b_1, \dots$ and convergents
$P_n / Q_n$, where $P_{-1} = 1$, $Q_{-1} = 0$, $P_0 = b_0$, $Q_0 = 1$,
$P_{n+1} = b_{n+1} P_n + P_{n-1}$ and $Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$. For a Laurent series
$y = \sum_m c_m x^{-m}$ let $v(y)$ be its order, the least $m$ with $c_m \ne 0$, and let
$v(0) = 0$; thus $|y| = |x|^{-v(y)}$ for $y \ne 0$. For $\beta \in K((x^{-1}))$ write
$[b_k, \dots, b_n, \beta] = b_k + 1/(b_{k+1} + 1/(\cdots + 1/(b_n + 1/\beta)))$. Then:
(i) for every $n \ge 0$ and every $\beta \ne 0$ such that $[b_k, \dots, b_n, \beta] \ne 0$ for
all $1 \le k \le n$, $(\beta P_n + P_{n-1}) / (\beta Q_n + Q_{n-1}) = [b_0, \dots, b_n, \beta]$;
(ii) $P_n Q_{n-1} - P_{n-1} Q_n = (-1)^{n+1}$ for every $n \ge 0$;
(iii) $Q_{n-1} \ne 0$ and $v(Q_n) < v(Q_{n-1})$ for every $n \ge 1$;
(iv) $v(Q_n) = v(b_1) + \dots + v(b_n)$ for every $n \ge 1$;
(v) $v(\alpha - P_n / Q_n) = -v(b_{n+1}) - 2 v(Q_n)$ for every $n \ge 1$;
(vi) $v(Q_n \alpha - P_n) < v(Q_{n+1} \alpha - P_{n+1})$ for every $n \ge 1$.

Part (iii) fails at $n = 0$ because $Q_{-1} = 0$.

## Sources

- Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Lemma 1.
