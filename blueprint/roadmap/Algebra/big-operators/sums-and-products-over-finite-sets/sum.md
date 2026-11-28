# Sum over a finite set

Let $M$ be an additive commutative monoid, $s$ a finite set of elements of a type $\iota$ (a term of `Finset ι`) and
$f \colon \iota \to M$. The sum $\sum_{i \in s} f(i) \in M$ adds the values $f(i)$ over the elements $i$ of $s$, each
taken once: Mathlib defines it as the sum of the multiset of the values of $f$ on the multiset underlying $s$. It is
written `∑ i ∈ s, f i`. For $s = \{0, 1, \dots, n - 1\}$ (`Finset.range n`), it is written
$\sum_{i=0}^{n-1} f(i)$.
