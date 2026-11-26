# Gessel word

Let $n$ be a natural number. For a word $u$ over the Gessel alphabet over
$S = [n] = \{1, \dots, n\}$ and a natural number $m$, write $\beta_u(m)$ for the signed balance of
$m$ in $u$: the number of occurrences of the unbarred letter $m$ in $u$ minus the number of
occurrences of the barred letter $\bar{m}$ in $u$. A word $w$ over this alphabet is a Gessel word
when, for every prefix $w'$ of $w$ (including the empty word and $w$ itself) and every $k$ with
$1 \le k \le n$, we have $\sum_{i=1}^{k} \beta_{w'}(n + 1 - i) \ge 0$, that is, the signed
balances in $w'$ of the $k$ largest labels $n, n - 1, \dots, n + 1 - k$ have nonnegative sum.
