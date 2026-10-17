---
article_id: af_e950c395762f6fefcb5186dc
declaration: theorem
origin: cited
lean: AlgorithmicLLL.fix_recursive_calls_prob_bound
---

# Lemma 6.6.8 (The number of recursive calls to fix)

Fix a $k$-CNF on $n$ variables where every clause shares variables with at most $2^{k-3}$ other clauses. Also fix a clause $C_0$ and some assignment of variables. Then, in an execution of $\operatorname{fix}(C_0)$, for any positive integer $\ell$, $\mathbb{P}(\text{there are at least } \ell \text{ recursive calls to fix in Line 7}) \leq 2^{-\ell+n+1}$. It follows that the expected number of recursive calls to fix is $n + O(1)$. Thus, in the Moser algorithm (Algorithm 6.6.5), the expected total number of calls to fix is $mn + O(m)$, where $n$ is the number of variables and $m$ is the number of clauses.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 6, Section 6.6](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
