# Unification of ranked terms through the curried encoding

Let $\Sigma$ be a ranked signature, a set of function symbols $f$ with arities $\mathrm{ar}(f) \ge 0$, and let $T(\Sigma, V)$ be the first-order terms over $\Sigma$ and variables $V = \{x_0, x_1, \dots\}$. The [unification terms](term.md) over the constant set $\Sigma$ are variables, constants, and binary nodes $\langle l, r \rangle$. The *curried encoding* $\ulcorner \cdot \urcorner$ is defined by:
- $\ulcorner x_i \urcorner = x_i$;
- $\ulcorner f(t_1, \dots, t_n) \urcorner = \langle \cdots \langle \langle f, \ulcorner t_1 \urcorner \rangle, \ulcorner t_2 \urcorner \rangle \cdots, \ulcorner t_n \urcorner \rangle$, which is just $f$ when $n = 0$.

A substitution $\sigma$ on ranked terms is encoded pointwise, by $\ulcorner \sigma \urcorner(x) = \ulcorner \sigma(x) \urcorner$.

**Theorem.**
1. The encoding is injective, and $\ulcorner t\sigma \urcorner = \ulcorner t \urcorner \ulcorner \sigma \urcorner$ for every term $t$ and substitution $\sigma$.
2. A ranked substitution $\sigma$ unifies a list of ranked equations $s_k = t_k$ if and only if $\ulcorner \sigma \urcorner$ unifies $\ulcorner s_k \urcorner = \ulcorner t_k \urcorner$. (An arbitrary substitution on unification terms need not preserve encoded terms: $x \mapsto \langle y, z \rangle$ sends $\ulcorner f(x) \urcorner$ to $\langle f, \langle y, z \rangle \rangle$, which encodes no ranked term.)
3. If the Martelli–Montanari algorithm returns a substitution $\theta$ on the encoded equations, then $\theta$ maps every variable occurring in them to an encoded term. The decoded substitution is a most general unifier of the ranked equations. If the algorithm fails, the ranked equations have no unifier.

**Proof.**
1. Both claims follow by induction on $t$. An encoded term determines its head symbol and its argument list, because the leftmost leaf of the spine of binary nodes is the head $f$ and the right children are the arguments.
2. Unifiers of encoded terms can be taken to send each variable to a subterm of an encoded term. A subterm at an argument position is encoded, so the unifier is the encoding of a ranked substitution. The equivalence then follows from part 1 and injectivity.
3. The returned $\theta$ is a most general unifier of the encoded equations, by [correctness of the algorithm](is-mgu-unify.md). In encoded terms, variables occur only as whole terms or as right children of binary nodes, never as left children. Decomposition steps therefore only ever pair a variable with an encoded term, so every binding of $\theta$ is an encoded term. Applying part 2 to $\theta$ and to any other unifier transfers generality.

Arity is respected automatically: encoded terms with the same head but different numbers of arguments have spines of different lengths, so they never unify.

## Depends on

- [Terms for unification](term.md)

## Proof depends on

- [Unification returns a most general unifier](is-mgu-unify.md)

## Sources

- A. Martelli and U. Montanari, "An efficient unification algorithm", *ACM Transactions on Programming Languages and Systems* 4(2):258–282, 1982, <https://courses.grainger.illinois.edu/cs576/sp2017/readings/01-jan-19/martelli-montanari-unif.pdf>, Introduction (unification of first-order terms and most general unifiers). The curried encoding and the transfer argument are written out here.
