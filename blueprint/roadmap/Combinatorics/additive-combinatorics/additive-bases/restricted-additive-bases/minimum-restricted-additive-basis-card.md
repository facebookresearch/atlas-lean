# Minimum size of a restricted additive basis

Let $s$ be a natural number. A restricted
additive basis of $\{0, 1, \dots, s\}$ is a finite set $A$ of natural numbers with $2a \le s$ for
every $a \in A$ such that every natural number $x \le s$ can be written as $x = a + b$ with
$a, b \in A$, where $a = b$ is allowed. The minimum restricted additive basis size $k^*(s)$ is
the smallest cardinality of a restricted additive basis of $\{0, 1, \dots, s\}$; it is undefined
when no restricted additive basis of $\{0, 1, \dots, s\}$ exists.

The restriction $2a \le s$ is imposed for odd $s$ as well as for even $s$.

## Sources

- Jukka Kohonen, Visa Koivunen, and Robin Rajamäki, *Planar Additive Bases for Rectangles*, Journal of Integer Sequences 21 (2018), Article 18.9.8: additive-basis notion (`A + A ⊇ [0, n]`), lines 126–128; one-dimensional restricted basis (`A ⊆ [0, n/2]`), lines 170–171; minimum restricted-basis notation `k^*`, lines 200–203, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Rajamaki/raj.tex>. The one-dimensional `k^*(s, 0)` notion supports G. Yu's restricted 2-basis bound (`s_x / k^*(s_x, 0)^2 ≤ 0.41983`, equation `eq:yu_restr`, lines 897–901), quoting G. Yu, *Upper bounds for finite additive 2-bases*, Proc. Amer. Math. Soc. 137 (2009), 11–18, Theorem 1.2.
