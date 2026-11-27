# Lower bound for $\log F_9(n)$

Let $w_9$ be the table of divisors $d$ of $Q_9 = 210$
paired with their Möbius values $\varepsilon$, and for a natural number $n$ let

$$\log F_9(n) = \sum_{(d, \varepsilon) \in w_9}
\varepsilon \log \frac{(10 n k_d)!}{(9 n k_d)!\,(n k_d)!}, \qquad k_d = 210/d.$$

Then for every natural number $n \ge 1$,

$$48 n (10 \log 10 - 9 \log 9) - 16 - 48 \log(2100 n) \le \log F_9(n).$$
