# Erdős Problem 539: square-root lower bound for the cofactor threshold

For a natural number
$n$, let $h(n)$ be the largest natural number $m$ such that for every set $A$ of exactly $n$
positive integers, the set $\{a/\gcd(a,b) : a, b \in A\}$ has at least $m$ elements. Then
$\sqrt{n} = O(h(n))$ as $n \to \infty$: there are a real constant $C$ and an $n_0$ such that
$\sqrt{n} \le C\,h(n)$ for all natural numbers $n \ge n_0$.

This lower bound was proved by Erdős and Szemerédi. The exact order of growth of $h(n)$ is a
separate question.

## Sources

- Johannes Schmitt, Tim Gehrunger, Jasper Dekoninck, Gergely Bérczi, Uri Kreitner, Liam Price, and David Holmes, *ProofCouncil: An LLM Agent for Solving Open Mathematical Problems*, arXiv:2607.09474 (2026), https://arxiv.org/abs/2607.09474.
