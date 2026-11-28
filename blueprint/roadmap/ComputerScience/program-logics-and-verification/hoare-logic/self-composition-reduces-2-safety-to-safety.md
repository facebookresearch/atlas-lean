# Self-composition reduces 2-safety to safety

Two forms of self-composition turn a property of pairs of executions into a property of single executions.

1. **Systems and $k$-products.** Let $S$ be a system, a set of infinite traces over states $\Sigma$. Its *$k$-product* $S^k$ is the system over $\Sigma^k$ whose traces combine $k$ traces of $S$ position by position. For every $k$-safety hyperproperty $K$ there is a safety property $\hat K$ over $\Sigma^k$ such that $S$ satisfies $K$ if and only if $S^k$ satisfies $\hat K$. The case $k = 2$ is the parallel self-composition $S \times S$.
2. **Programs, terminating runs.** For an IMP command $c$ and relations $\mathit{Pre}$ on pairs of initial states and $\mathit{Post}$ on pairs of final states, the following are equivalent:
    - for all $s_0, s_1$ with $\mathit{Pre}(s_0, s_1)$ and all terminating runs $\langle c, s_0\rangle \Downarrow t_0$ and $\langle c, s_1 \rangle \Downarrow t_1$, we have $\mathit{Post}(t_0, t_1)$;
    - the partial-correctness Hoare triple $\{\langle s_0, s_1 \rangle \mid \mathit{Pre}(s_0, s_1)\}\ c^{(0)} ; c^{(1)}\ \{\langle t_0, t_1 \rangle \mid \mathit{Post}(t_0, t_1)\}$ is valid, read on the sequential self-composition through the state pairing.

    For example, termination-insensitive noninterference of a deterministic command is the case where $\mathit{Pre}$ is equality on low variables and $\mathit{Post}$ is equality on low variables.

**Proof.**
1. This is Clarkson and Schneider's Theorem 2: the bad things of $K$, which are sets of at most $k$ finite traces, become single finite traces of $S^k$.
2. This follows from the [two-run product theorem](two-run-product-of-imp-commands.md): terminating runs of $c^{(0)} ; c^{(1)}$ from paired states correspond exactly to pairs of terminating runs of $c$.

Part 2 covers only properties of pairs of terminating runs. Properties that observe divergence or prefixes of executions, and possibilistic policies, which are hyperliveness, are not reduced this way.

## Depends on

- [Two-run product of IMP commands](two-run-product-of-imp-commands.md)

## Background

- [Hyperproperties, hypersafety and $k$-safety](../../../Logic/temporal-logic/temporal-specification/hyperproperties-hypersafety-and-k-safety.md)

## Sources

- M. R. Clarkson and F. B. Schneider, "Hyperproperties", *Journal of Computer Security* 18(6):1157–1210, 2010, <https://www.cs.cornell.edu/info/people/fbs/publications/Hyperproperties.pdf>, Section 4: sequential self-composition and its use for secure information flow (Barthe et al.), Terauchi and Aiken's 2-safety properties of deterministic programs, which ignore nonterminating traces, parallel self-composition and the $k$-product $S^k$, and Theorem 2 (every $k$-safety hyperproperty of $S$ reduces to a safety property of $S^k$). The footnote observes that hyperliveness formulations are not amenable to these reductions.
