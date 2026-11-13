# Exact Boyer–Moore cost when pattern and text repeat the same letter

Let $x$ be a letter
of the alphabet $\{0, \dots, \sigma - 1\}$, let $m$ and $n$ be natural numbers with
$0 < m \le n$, and write $x^k$ for the word of $k$ copies of $x$. The cost of the Boyer–Moore
matcher with pattern $x^m$ and text $x^n$ equals $m + n + P + (m + 4)(n - m + 1)$, where $P$ is
the cost of the Boyer–Moore preprocessing of the pattern $x^m$.

Of this cost, $m(n - m + 1)$ counts character tests: every alignment is a match and compares all
$m$ pattern letters.
