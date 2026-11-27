# Every nonempty set of natural numbers has a least element

Every nonempty set $A$ of natural numbers has a least element: some $m \in A$ with $m \le n$ for all $n \in A$. Mathlib states this more explicitly, naming the least element. Let $s$ be a nonempty set of natural numbers whose membership is decidable, which classical logic always allows. Then the number given by Mathlib's `Nat.find`, which tests $0, 1, 2, \dots$ in turn until it reaches an element of $s$, is a least element of $s$: it lies in $s$ and is at most every element of $s$. Set-theoretic presentations, such as Enderton's, construct the natural numbers as the set $\omega$ ordered by $m < n$ if and only if $m \in n$; this ordered set is isomorphic to the natural numbers with their usual order, so the statement is the same for it.

## Sources

- Herbert B. Enderton, Elements of Set Theory, Academic Press, 1977.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for least elements: `IsLeast`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Order/Bounds/Defs.lean#L45-L49.
