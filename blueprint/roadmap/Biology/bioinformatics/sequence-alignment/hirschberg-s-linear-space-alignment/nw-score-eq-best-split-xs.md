# Hirschberg split identity, splitting the first sequence

Fix a substitution score
$\sigma$ assigning an integer to each pair of letters and an integer gap score $g$, and write
$\mathrm{NW}$ for the Needleman–Wunsch score. For a sequence $s$, write $s_{\lt j}$ for its first
$j$ letters and $s_{\ge j}$ for the remaining letters. Let $x$, $y$ be sequences and
$m \le |x|$, and let $k$ be the first index $j \in \{0, \dots, |y|\}$ that maximizes
$\mathrm{NW}(x_{\lt m}, y_{\lt j}) + \mathrm{NW}(x_{\ge m}, y_{\ge j})$. Then
$\mathrm{NW}(x_{\lt m}, y_{\lt k}) + \mathrm{NW}(x_{\ge m}, y_{\ge k}) = \mathrm{NW}(x, y)$.
