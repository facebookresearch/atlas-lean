# Assignment rule with a store-irrelevant heap assertion

Let $x$ and $y$ be variables,
let $p$ and $q$ be predicates on stores, and let $H$ be a store-irrelevant heap assertion.
Write $s[x := n]$ for the store that agrees with $s$ except that it maps $x$ to $n$. If every
store $s$ satisfying $p$ has $q(s[x := s(y)])$, then the separation-logic triple for the
assignment $x := y$ is valid with precondition "$p(s)$ and $H(s, h)$" and postcondition
"$q(s)$ and $H(s, h)$", where $s$ is the store and $h$ the heap.

An assignment leaves the heap untouched, so no framing is needed.
