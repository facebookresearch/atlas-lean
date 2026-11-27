# Charleston-Steel recursion for the leaves needed to fix a maximum parsimony root state

Let $R$ be a set of $r \ge 2$ character states, $a \in R$, and let $T_k$ be the fully bifurcating rooted tree of height $k$ (with $2^k$ leaves). For a character $f$ on the leaves, Fitch's bottom-up pass assigns each leaf $\{f(\ell)\}$ and each internal vertex with children labeled $A, B$ the set $A * B$, where $A * B = A \cap B$ if $A \cap B \neq \emptyset$ and $A * B = A \cup B$ otherwise; the root label $X_\rho$ is exactly the set of maximum parsimony root states. For $A \subseteq R$ with $a \in A$ and $|A| \le 2^k$, let $f_{k,r}^A$ be the minimum number of leaves in state $a$ over all characters with $X_\rho = A$, and $f_{k,r} = f_{k,r}^{\{a\}}$, the minimum number of $a$-leaves for which maximum parsimony unambiguously reconstructs $a$ at the root. By the standard decomposition of $T_{k+1}$ into two copies of $T_k$,

$$ f_{k+1,r}^A = \min\bigl\{ f_{k,r}^B + f_{k,r}^C : B, C \subseteq R,\ |B|, |C| \le 2^k,\ B * C = A \bigr\}. $$

Charleston and Steel conjectured that $f_{k,r} = f_{k-p,r} + f_{k-p-1,r}$ when $r = 2p$, and $f_{k,r} = 2 f_{k-p,r}$ when $r = 2p - 1$.

**Main Theorem 2 (even number of states).** Let $r = 2p$, $p \ge 1$. For $k \ge r$, wherever the quantities are defined,

$$ f_{k+1,r} = f_{k-p+1,r} + f_{k-p,r}. $$

The initial values satisfy $f_{0,r} = 1$, $f_{k,r} = 2$ for $1 \le k \le p$, $f_{p+1,r} = 3$, and $f_{k,r} \le 4$ for $p+1 < k \le r$. So the conjecture holds for every even $r$, in particular for $r = 4$ (nucleotides) and $r = 20$ (amino acids).

**Odd number of states.** The conjecture fails in general for odd $r$: for $r = 2p - 1$, $p \ge 2$, it predicts $f_{p+1,r} = 2 f_{1,r} = 4$, but in fact $f_{p+1,r} = 3$ (Observation 1). For $r = 3$ (Main Theorem 1), $f_{2,3} = 2$, $f_{3,3} = 3$, and for all $k \ge 3$, $f_{k+1,3} = 2 f_{k,3}^{A_2} = 2 f_{k-1,3}$, where $A_2$ is any two-element set containing $a$. The recursion therefore holds for $r = 3$ once the initial conditions are adjusted.

General monotonicity facts used along the way: $f_{k,r}^A \le f_{k,r}^B$ whenever $|A| \ge |B|$ and $a \in A \cap B$; $f_{k,r}^A \le f_{k+1,r}^A$; $f_{k+1,r}^{A_i} = f_{k,r}^{A_{i-1}} = f_{k-(i-2),r}$ for nested sets $A_i \ni a$ of size $i$; and $f_{k+1,r}^{A_i} \le f_{k+1,\tilde r}^{A_i}$ for $\tilde r \le r$.

## Depends on

- [Fitch's algorithm](../../small-parsimony-problem/fitch.md)
- [Fitch's root set is the set of optimal root states](../../small-parsimony-problem/fitch-set-eq.md)

## Expansion

Fitch's operation gives the recursion for $f_{k+1,r}^A$ directly: the root set is $B * C$ for the root sets $B, C$ of the two subtrees, and the subtrees can be filled independently. The difficulty is the minimum over all pairs $(B, C)$. Lemmas on how $f^A$ depends only on $|A|$, and its monotonicity in $|A|$, $k$ and $r$, reduce the minimum to a short list of candidates (Corollary 1): to get $\{a\}$ at the root one either intersects $\{a\}$ with a large set, or intersects two sets containing $a$ whose other states are disjoint. Identifying $f_{k,r}^{A_i}$ with $f_{k-i+2,r}$ (Theorem 3) turns each candidate into a sum of two values of $f_{\cdot,r}$, and comparing them with the monotonicity in $k$ shows that for $r = 2p$ and $k \ge r$ the minimum equals $f_{k-p+1,r} + f_{k-p,r}$. The small cases $k < r$ are settled directly by explicit characters (Lemma 2). For odd $r$ the extra candidate $2 f_{k,r}^{A_1 \cup D_{p-1}}$ appears, and a direct construction on $T_{p+1}$ with three $a$-leaves refutes the predicted value $4$.

## Sources

- Lina Herbst, Mareike Fischer, "Ancestral Sequence Reconstruction with Maximum Parsimony", Bulletin of Mathematical Biology 79 (2017), 2865–2886, <https://doi.org/10.1007/s11538-017-0354-6>. Published version of arXiv:1702.01436, cited next; locators there refer to the arXiv version.
- Lina Herbst, Mareike Fischer, "Ancestral sequence reconstruction with Maximum Parsimony", arXiv (2017). Conjecture 1, Observation 1, Lemma 1, Theorems 1-4, Corollary 1, Main Theorems 1 and 2, Lemma 2. <https://doi.org/10.48550/arXiv.1702.01436>
