# Basic CBC-MAC is insecure for variable-length messages

Let $K$ be a finite nonempty key type, $X$ an additive commutative group with decidable equality, $E : K \to \mathrm{Perm}(X)$ any block cipher and $x \in X$. Against [variable-length CBC-MAC](cbc-mac-var-scheme.md) built from $E$, the [length-extension forger](length-ext-forger.md) for $x$ has forgery advantage exactly $1$. In the [forgery experiment](../../security-games/generic-security-games/mac-game.md) a key $k$ is drawn uniformly, the forger runs with the tagging oracle, and it wins iff its output verifies under $k$ and its output message was never queried.

The forger asks once, for the tag $t = E_k(0 + x) = E_k(x)$ of $[x]$, and outputs the two-block message $[x, x - t]$, which differs from $[x]$, with tag $t$. Its tag is

$$
E_k\bigl(E_k(x) + (x - t)\bigr) = E_k(t + x - t) = E_k(x) = t,
$$

using commutativity of addition in $X$. The result covers every block cipher on such a group; it is not a statement about permutations of an arbitrary set without this structure.
