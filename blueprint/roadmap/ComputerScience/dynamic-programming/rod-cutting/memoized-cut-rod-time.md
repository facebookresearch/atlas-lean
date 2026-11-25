# Event count of memoized rod cutting

Let $\alpha$ be an additive commutative monoid with a
linear order and let $p \in \alpha^n$ be a vector of prices. The memoized cut-rod procedure on $p$
charges exactly $n^2 + 2n + 2$ events, where one event is charged per cache probe, per first-cut
candidate, and per cache write.

Allocation, initialization, arithmetic, comparisons and control are not charged.
