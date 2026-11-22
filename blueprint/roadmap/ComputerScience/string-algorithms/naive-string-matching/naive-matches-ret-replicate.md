# Naive matching on a repeated symbol reports every shift

Let $\alpha$ be a type whose
Boolean equality is reflexive, let $x \in \alpha$, and let $m \le n$ be natural numbers. On the
pattern consisting of $m$ copies of $x$ and the text consisting of $n$ copies of $x$, the naive
matcher reports exactly the shifts $0, 1, \dots, n - m$ in increasing order, so all overlapping
occurrences are reported.
