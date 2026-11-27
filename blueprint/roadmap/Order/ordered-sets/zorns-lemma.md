# Zorn's lemma

Let $P$ be a set with a reflexive and transitive relation $\le$, for instance a partially ordered set, in which every chain has an upper bound in $P$, where a *chain* is a subset of $P$ any two of whose elements are comparable. The empty chain is included, so $P \neq \varnothing$. Then $P$ has a maximal element: some $m \in P$ such that $m \le p$ implies $p \le m$ for every $p \in P$. When $\le$ is a partial order, this says that no $p \in P$ satisfies $m < p$.

## Sources

- Herbert B. Enderton, Elements of Set Theory, Academic Press, 1977.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for maximal elements of a preordered set, defined as the order dual of minimal elements: `IsMin`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Order/Max.lean#L141-L149.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for chains: `IsChain`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Order/Preorder/Chain.lean#L50-L52.
