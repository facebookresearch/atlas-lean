# No countably additive congruence-invariant measure on all plane sets

No function $\mu$ on all subsets of $\mathbb{R}^2$ with values in $[0, \infty]$ is congruence invariant,
countably additive and equal to Carathéodory's linear measure on Borel sets: the countably additive
reading of Problem 169 has a negative answer in ZFC.

Sketch: let $V_0 \subseteq [0, 1]$ meet each coset of $\mathbb{Q}$ in $\mathbb{R}$ exactly once (a
Vitali selector) and put $V = V_0 \times \{0\}$. Enumerating $\mathbb{Q} \cap [-1, 1]$ as $(q_n)$, the
translates $T_n = V + (q_n, 0)$ are pairwise disjoint and each congruent to $V$, so all have the
same mass $c = \mu(V)$. Their union $U$ contains the segment $[0, 1] \times \{0\}$ of linear measure
$1$ and lies in the segment $[-1, 2] \times \{0\}$ of linear measure $3$, so countable additivity and
monotonicity give $1 \le \mu(U) \le 3$, while countable additivity also gives $\mu(U) = \sum_n c$,
which is $0$ if $c = 0$ and $\infty$ if $c > 0$, a contradiction. With $V = V_0 \times [0, 1]$, the unit
square and the strip $[-1, 2] \times [0, 1]$, the same argument shows that no such $\mu$ extends plane
Lebesgue measure either.

This settles the countably additive reading only. The typescript says bare "additive". For finitely
additive functions and plane Lebesgue measure, Banach's 1923 theorem gives a positive answer: there is
a finitely additive, isometry-invariant function on all plane sets extending Lebesgue measure (a
Banach measure).

## Sources

- E. Szpilrajn, Problem 169 of the Scottish Book; typescript PDF p.78, printed p.75, <http://kielich.amu.edu.pl/Stefan_Banach/pdf/ks-szkocka/ks-szkocka3ang.pdf>.
- S. Banach, *Sur le problème de la mesure*, Fund. Math. 4 (1923), 7–33.
- C. Carathéodory, *Über das lineare Mass von Punktmengen, eine Verallgemeinerung des Längenbegriffs*,
  Nachr. Ges. Wiss. Göttingen (1914), 404–426 (the linear measure of plane sets).
