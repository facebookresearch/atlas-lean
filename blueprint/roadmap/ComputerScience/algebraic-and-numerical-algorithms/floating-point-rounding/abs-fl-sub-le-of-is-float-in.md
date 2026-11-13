# Round to nearest in a bounded format

Let $K$ be a linearly ordered field with a floor
function, let $p \ge 1$, and let $q_{\min}$ and $q_{\max}$ be integers. For every $x \in K$ and
every number $f$ of the binary format with $p$-bit significands and last-place exponents in
$[q_{\min}, q_{\max}]$, the rounding $\mathrm{fl}(x)$ of $x$ to nearest, ties to even, with
$p$-bit significands satisfies $|\mathrm{fl}(x) - x| \le |f - x|$.
