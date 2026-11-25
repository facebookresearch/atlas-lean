# Parking-function shuffles

Let $m'$, $n$, $k$ be natural numbers and let
$\pi : \{0, \dots, m' - 1\} \to \{0, \dots, n - 1\}$, with one-based letters $w_i = \pi(i) + 1$.
Then $\pi$ is a parking-function shuffle with parameters $(m', n, k)$ when all of the following
hold: no letter $w_i$ equals $k$; exactly $\max(m' + k - n, 0)$ letters satisfy $w_i < k$;
exactly $\max(n - k, 0)$ letters satisfy $w_i > k$; for every $s$ with $1 \le s \le k - 1$, at
most $k - s$ letters satisfy $s \le w_i \le k - 1$; and for every $s$ with $k + 1 \le s \le n$, at
most $n + 1 - s$ letters satisfy $w_i \ge s$.

With $m = m' + 1$, the word $(w_0, \dots, w_{m'-1})$ plays the role of the source's
$(\pi_2, \dots, \pi_m)$, and the conditions express membership in the source's set
$\mathrm{Sh}_m(k - 1, n - k)$ of shuffles of a parking function of $m - n + k - 1$ cars on
$k - 1$ spots (the letters below $k$) with a parking function of length $n - k$ shifted up by
$k$ (the letters above $k$): parking-function membership does not depend on the order of the
letters, and the last two conditions are the usual counting criterion for every car to park.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Section 4, Definition of `(m, n)`-parking function shuffles (`Sh_m(k - 1, n - k)`).
