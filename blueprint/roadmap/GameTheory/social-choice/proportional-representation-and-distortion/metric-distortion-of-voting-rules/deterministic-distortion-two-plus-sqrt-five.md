# A deterministic rule with metric distortion 2 + sqrt(5)

There is a polynomial-time deterministic voting rule with metric distortion at most $2 + \sqrt 5 \approx 4.236$; in particular the uncovered-set bound $5$ is not optimal. For $\lambda \in [\tfrac12, 1]$, the $\lambda$-weighted uncovered set consists of the candidates $a$ such that for every other candidate $b$, either at least $(1 - \lambda) n$ voters prefer $a$ to $b$, or there is a candidate $c \notin \{a, b\}$ such that at least $(1 - \lambda) n$ voters prefer $a$ to $c$ and at least $\lambda n$ voters prefer $c$ to $b$. This set is nonempty for every $\lambda \in [\tfrac12, 1]$, and the rule that selects a candidate of the $\lambda$-weighted uncovered set for $\lambda = (\sqrt5 - 1)/2$ has distortion at most $2 + \sqrt 5$; for this family of rules the bound is tight.

## Proof sketch

Non-emptiness follows by examining a candidate that would violate the condition and walking down a chain of candidates whose pairwise margins cross the threshold $\lambda$. For the distortion bound, let $a$ be selected and $o$ optimal. If at least $(1 - \lambda) n$ voters prefer $a$ to $o$, a triangle-inequality argument over these voters bounds $\mathrm{SC}(a)/\mathrm{SC}(o)$; otherwise apply the same argument along the two-step path $a \to c \to o$. Optimizing the two resulting bounds over $\lambda$ gives $\lambda = (\sqrt5 - 1)/2$ and the constant $2 + \sqrt 5$. The same bound also follows from a linear-programming-duality framework in which an upper bound on distortion is certified by a flow of small cost.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Sources

- K. Munagala, K. Wang, "Improved Metric Distortion for Deterministic Social Choice Rules", EC 2019, arXiv:1905.01401.
- D. Kempe, "An Analysis Framework for Metric Voting based on LP Duality", AAAI 2020, arXiv:1911.07162.
