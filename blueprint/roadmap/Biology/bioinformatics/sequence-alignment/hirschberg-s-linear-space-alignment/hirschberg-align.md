# Hirschberg reconstruction with fuel

Fix a substitution score $\sigma$ assigning an
integer to each pair of letters and an integer gap score $g$, and write $\mathrm{NW}$ for the
Needleman–Wunsch score. For a sequence $s$, write $s_{\lt j}$ for its first $j$ letters and
$s_{\ge j}$ for the remaining letters. The Hirschberg reconstruction of sequences $x$ and $y$
with fuel $n$ is the alignment defined by recursion on $n$. With fuel $0$ it is the empty
alignment. With fuel $n + 1$: if $|x| \le 1$ and $|y| \le 1$, it is the base-case alignment
of $x$ and $y$; otherwise, if $|y| \ge |x|$, let $m = \lfloor |y|/2 \rfloor$ and let $k$ be
the first index $j \in \{0, \dots, |x|\}$ that maximizes
$\mathrm{NW}(x_{\lt j}, y_{\lt m}) + \mathrm{NW}(x_{\ge j}, y_{\ge m})$, and the result is the
concatenation of the reconstructions with fuel $n$ of $x_{\lt k}$ and $y_{\lt m}$ and of $x_{\ge k}$
and $y_{\ge m}$; otherwise, let $m = \lfloor |x|/2 \rfloor$ and let $k$ be the first index
$j \in \{0, \dots, |y|\}$ that maximizes
$\mathrm{NW}(x_{\lt m}, y_{\lt j}) + \mathrm{NW}(x_{\ge m}, y_{\ge j})$, and the result is the
concatenation of the reconstructions with fuel $n$ of $x_{\lt m}$ and $y_{\lt k}$ and of $x_{\ge m}$
and $y_{\ge k}$.

Hirschberg's alignment algorithm runs this reconstruction with fuel $|x| + |y|$.
