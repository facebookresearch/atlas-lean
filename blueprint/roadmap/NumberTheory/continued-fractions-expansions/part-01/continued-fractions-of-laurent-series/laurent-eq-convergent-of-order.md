# Close rational approximations and convergents

Let $K$ be a field and let
$\alpha \in K((x^{-1}))$ be irrational, with partial quotients $b_0, b_1, \dots$ and convergents
$P_n / Q_n$, where $P_{-1} = 1$, $Q_{-1} = 0$, $P_0 = b_0$, $Q_0 = 1$,
$P_{n+1} = b_{n+1} P_n + P_{n-1}$ and $Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$. For a Laurent series
$y = \sum_m c_m x^{-m}$ let $v(y)$ be its order, the least $m$ with $c_m \ne 0$, and let
$v(0) = 0$. Let $P, Q \in K[x]$ be coprime with $Q \ne 0$.
(i) If $v(Q \alpha - P) = s + \deg Q$ for some integer $s \ge 1$, then there are $n \ge 0$ and
$c \in K \setminus \{0\}$ with $P = c P_n$, $Q = c Q_n$ and $v(b_{n+1}) = -s$.
(ii) If $v(Q \alpha - P) = \deg Q$, then there are $n \ge 0$ and $c, d \in K \setminus \{0\}$
with $P = c P_n + d P_{n-1}$ and $Q = c Q_n + d Q_{n-1}$.

With $|y| = |x|^{-v(y)}$, the hypothesis of (i) reads $|Q \alpha - P| = |x|^{-s} |Q|^{-1}$ and
its conclusion $|b_{n+1}| = |x|^s$; the hypothesis of (ii) reads $|Q \alpha - P| = |Q|^{-1}$.

## Sources

- Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Lemma 3 (generalizing Baum and Sweet, Lemma 1).
