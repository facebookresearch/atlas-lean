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
2. By part 1, $\ulcorner s\sigma \urcorner = \ulcorner s \urcorner \ulcorner \sigma \urcorner$ and $\ulcorner t\sigma \urcorner = \ulcorner t \urcorner \ulcorner \sigma \urcorner$, so by injectivity $s\sigma = t\sigma$ if and only if $\ulcorner s \urcorner \ulcorner \sigma \urcorner = \ulcorner t \urcorner \ulcorner \sigma \urcorner$.
3. Call a unification term *full* if it is a variable or the encoding of a ranked term, and *partial* if it is a spine $\langle \cdots \langle f, \ulcorner t_1 \urcorner \rangle \cdots, \ulcorner t_k \urcorner \rangle$ with $k < \mathrm{ar}(f)$. In a full or partial term, every left child of a binary node is partial and every right child is full, so variables occur only at full positions. Every step of the Martelli–Montanari algorithm preserves the invariant that each equation pairs two full terms or two partial terms. Decomposing $\langle l, r \rangle = \langle l', r' \rangle$ pairs the two left children, both partial, and the two right children, both full; deleting and orienting equations keep it; and an elimination step $x = u$ has $u$ full, because $x$ is, so $u$ is the encoding of a ranked term and, by part 1, substituting it maps full terms to full terms and partial terms to partial terms. Hence every binding of the returned $\theta$, and of every composition of bindings formed by the algorithm, is the encoding of a ranked term, so $\theta = \ulcorner \tau \urcorner$ for a ranked substitution $\tau$. By [correctness of the algorithm](is-mgu-unify.md), $\theta$ is a most general unifier of the encoded equations, so by part 2 $\tau$ unifies the ranked equations. If $\sigma$ is any ranked unifier, then $\ulcorner \sigma \urcorner$ unifies the encoded equations, so $\ulcorner \sigma \urcorner(x) = \theta(x)\rho$ for every variable $x$ of the equations and some substitution $\rho$. Each variable $y$ of $\theta(x)$ occurs at a full position, so $\rho(y)$ is a subterm of the encoded term $\ulcorner \sigma(x) \urcorner$ at a full position and is itself the encoding of a ranked term. Hence $\rho$ is, on these variables, the encoding of a ranked substitution $\rho'$, and by part 1 $\sigma(x) = \tau(x)\rho'$, so $\tau$ is more general than $\sigma$. If the algorithm fails, the encoded equations have no unifier, and by part 2 neither have the ranked ones.

Arity is respected automatically: encoded terms with the same head but different numbers of arguments have spines of different lengths, so they never unify.

## Depends on

- [Terms for unification](term.md)

## Proof depends on

- [Unification returns a most general unifier](is-mgu-unify.md)

## Sources

- A. Martelli and U. Montanari, "An efficient unification algorithm", *ACM Transactions on Programming Languages and Systems* 4(2):258–282, 1982, <https://courses.grainger.illinois.edu/cs576/sp2017/readings/01-jan-19/martelli-montanari-unif.pdf>, Introduction (unification of first-order terms and most general unifiers). The curried encoding and the transfer argument are written out here.
