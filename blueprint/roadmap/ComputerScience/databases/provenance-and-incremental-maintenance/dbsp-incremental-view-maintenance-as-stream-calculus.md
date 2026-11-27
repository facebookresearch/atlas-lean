# DBSP: incremental view maintenance as stream calculus

Let $A$ be an abelian group and consider streams $s : \mathbb{N} \to A$. Integration $I$ (running sum) and
differentiation $D$, with $D(s)[t] = s[t] - s[t-1]$ and $s[-1] = 0$, are mutually inverse causal linear
time-invariant operators; $z^{-1}$ denotes the delay by one step. For a stream operator $Q$ define its incremental
version $Q^\Delta = D \circ Q \circ I$. Then:

1. (chain rule) $(Q_1 \circ Q_2)^\Delta = Q_1^\Delta \circ Q_2^\Delta$;
2. every linear time-invariant operator $Q$ satisfies $Q^\Delta = Q$;
3. for a bilinear time-invariant operator $\times$ and streams of changes $a, b$,

    $$(a \times b)^\Delta = a \times b + z^{-1}(I(a)) \times b + a \times z^{-1}(I(b)).$$


Applied to relational operators lifted to streams of $\mathbb{Z}$-relations, these rules give incremental
versions of relational queries.

## Proof depends on

- [Z-relations and delta rules for incremental maintenance](z-relations-and-delta-rules-for-incremental-maintenance.md)

## Sources

- M. Budiu, F. McSherry, L. Ryzhyk and V. Tannen, *DBSP: Automatic incremental view maintenance for rich query languages*, VLDB 2023, arXiv:2203.16684, Proposition 3.2, Theorem 3.3 and Theorem 3.4. <https://arxiv.org/pdf/2203.16684>
