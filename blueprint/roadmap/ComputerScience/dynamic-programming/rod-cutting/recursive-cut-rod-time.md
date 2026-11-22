# Running time of recursive CUT-ROD

Let $\alpha$ be an additive commutative monoid with a
linear order, and let $p_1, \dots, p_n \in \alpha$ be prices. Recursive CUT-ROD on these prices,
which charges one tick per invocation, makes exactly $2^n$ invocations, counting the root call
and every call on an empty rod, whatever the prices are.
