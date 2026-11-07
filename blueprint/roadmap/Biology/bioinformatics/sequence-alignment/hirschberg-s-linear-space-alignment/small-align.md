# Base-case alignment for Hirschberg

Fix a substitution score $\sigma$ assigning an
integer to each pair of letters and an integer gap score $g$, and write a column as a pair
whose missing entry, a gap, is marked $\bot$. The base-case alignment of sequences $x$ and $y$
is the empty alignment if both are empty; the single column $(\bot, b)$ if $x$ is empty and
$y = [b]$; the single column $(a, \bot)$ if $x = [a]$ and $y$ is empty; if $x = [a]$ and
$y = [b]$, it is the single column $(a, b)$ when $\sigma(a, b) \ge 2g$ and the two columns
$(a, \bot)$, $(\bot, b)$ otherwise; and it is the empty alignment when $x$ or $y$ has length
at least $2$.
