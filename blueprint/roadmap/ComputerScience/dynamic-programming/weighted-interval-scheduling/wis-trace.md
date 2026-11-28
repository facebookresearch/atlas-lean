# Traceback of the weighted interval scheduling recurrence

For intervals indexed by the
positive integers with start times $s$, finish times $f$ and weights $w$, and with
$\mathrm{OPT}$ and $p$ as in the weighted interval scheduling recurrence, the traceback is
$T(0) = \emptyset$ and, for $j \ge 1$, $T(j) = \{j\} \cup T(p(j))$ if
$\mathrm{OPT}(j - 1) < w(j) + \mathrm{OPT}(p(j))$ and $T(j) = T(j - 1)$ otherwise.
