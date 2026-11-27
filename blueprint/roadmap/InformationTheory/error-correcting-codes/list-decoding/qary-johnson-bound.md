# Integer q-ary Johnson bound

Let $\alpha$ be a finite alphabet with $q = |\alpha| \ge 2$ letters, let $n, d, e$ be natural numbers with $q e \le (q-1) n$, let $y \in \alpha^n$, and let $S \subseteq \alpha^n$ be a finite set of words whose distinct elements are at Hamming distance at least $d$ and which all lie within Hamming distance $e$ of $y$. Then, computing in the integers (so $n - e$ and $n - d$ may be negative),

$$|S| \bigl((q-1)(n-e)^2 + e^2 - (q-1)\,n\,(n-d)\bigr) \le (q-1)\,n\,d.$$

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 7.3.1.
- Guruswami and Sudan, "Extensions to the Johnson bound", 2001, Theorem 1.
