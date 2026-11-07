# Hirschberg recursion step splitting the second sequence

Fix a substitution score
$\sigma$ assigning an integer to each pair of letters and an integer gap score $g$, and write
$\mathrm{NW}$ for the Needleman–Wunsch score. For a sequence $s$, write $s_{\lt j}$ for its first
$j$ letters and $s_{\ge j}$ for the remaining letters. Let $x$, $y$ be sequences with
$|y| \ge |x|$ that do not both have length at most $1$, let $m = \lfloor |y|/2 \rfloor$, and
let $k$ be the first index $j \in \{0, \dots, |x|\}$ that maximizes
$\mathrm{NW}(x_{\lt j}, y_{\lt m}) + \mathrm{NW}(x_{\ge j}, y_{\ge m})$. Then for every natural
number $n$, the Hirschberg reconstruction of $x$ and $y$ with fuel $n + 1$ is the
concatenation of the Hirschberg reconstruction of $x_{\lt k}$ and $y_{\lt m}$ with fuel $n$ and the
Hirschberg reconstruction of $x_{\ge k}$ and $y_{\ge m}$ with fuel $n$.
