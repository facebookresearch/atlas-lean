# Weighted interval scheduling recurrence

For intervals indexed by the positive integers with
start times $s$ and finish times $f$ in a linear order and weights $w$ in a commutative additive
monoid with a linear order, $\mathrm{OPT}(0) = 0$ and
$\mathrm{OPT}(j) = \max(\mathrm{OPT}(j - 1), w(j) + \mathrm{OPT}(p(j)))$ for $j \ge 1$, where $p(j)$
is the largest $i$ with $1 \le i < j$ and $f(i) \le s(j)$, or $0$ if there is none.
