# Delays needed to eliminate a motif-avoidant attractor

Let a Boolean network on $N$ variables, updated asynchronously, have a motif-avoidant attractor $A$ (an attractor contained in no minimal trap space) and let $T$ be a minimal trap space it avoids. A **linear extension** (delay) of a regulatory edge $j \to i$ inserts a new variable $z$ with $f_z = x_j$ and replaces $x_j$ by $z$ in $f_i$; it doubles the state space. Let $d \le N$ be the number of variables that oscillate in $A$, and $m < d$ the minimal number of oscillating variables on which a state of $A$ disagrees with the fixed values of $T$.

1. **Upper bound.** $A$ can be eliminated (no attractor of the delay-expanded network projects onto it) by linear extensions of at most

$$(N - d)(N - 1) + \frac{m(m + 1)}{2}$$

edges. If the smallest trap space containing both $A$ and $T$ has $M < N$ free variables, $N$ may be replaced by $M$. For a complete interaction graph with $E_{\max} = N^2$ edges, this is strictly less than $E_{\max}$, improving on the previous bound obtained by extending all edges until the graph is L-cuttable.
2. **Single delay.** If $N = d$ (or $M = d$) and $m = 1$, one linear extension suffices, namely of the self-regulation of the variable whose value differs between $A$ and $T$.
3. **Lower bound.** For the star-shaped family (complete interaction graph, point attractor $11\cdots1$, MAA consisting of $00\cdots0$ and the $N$ unit vectors), exactly $\lfloor N^2/4 \rfloor$ delays are necessary and sufficient. Hence no general bound can be below $\lfloor N^2/4 \rfloor \approx E_{\max}/4$.

Empirically, almost all MAAs found in random networks, and all those obtained from reduced biological models, are eliminated by a single linear extension.

## Depends on

- [Trap spaces and motif-avoidant attractors](trap-spaces-and-motif-avoidant-attractors.md)

## Expansion

A state outside a trap space that can reach it cannot belong to an attractor, so it suffices to build, in the delay-expanded network, a path from a state derived from $A$ into $T$. The subspace spanned by $A$ is not a trap space, so some escape transition exists; the algorithm aligns one variable at a time with $T$ by delaying its incoming edges from the oscillating variables, letting its update function read a stale state of the subspace in which the escape is enabled. Counting the delays used over the $N - d$ non-oscillating and the $m$ disagreeing oscillating variables gives item 1, and when only one variable disagrees and all variables oscillate, delaying its self-loop already opens the path, giving item 2. Delays must be chosen so that the memory states they create remain reachable from the canonical states of $A$; some delays fail because they create unreachable (Garden of Eden) memory states. In the star-shaped family, transitions inside the MAA can be reused, which is why fewer delays than the general bound suffice, yet a quadratic number is still forced.

## Sources

- S. Pastva, K. H. Park, O. Huvar, J. C. Rozum, R. Albert, "An open problem: Why are motif-avoidant attractors so rare in asynchronous Boolean networks?", *Journal of Mathematical Biology* (2025), Section 7 (linear extensions, Examples 9–10, upper and lower bounds on the number of delays) and Appendix A.1–A.3, <https://doi.org/10.1007/s00285-025-02235-8> (PMC12162798).
