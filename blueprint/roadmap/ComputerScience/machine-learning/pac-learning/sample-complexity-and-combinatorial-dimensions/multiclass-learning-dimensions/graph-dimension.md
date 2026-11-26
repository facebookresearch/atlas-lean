# Graph dimension of a multiclass concept class

Let $C$ be a set of functions $X \to \beta$. A set $W \subseteq X$ is G-shattered by $C$ if there is a reference labeling $f : X \to \beta$ such that for every $B \subseteq W$ some $c \in C$ agrees with $f$ on $B$ and disagrees with $f$ at every point of $W \setminus B$. The graph dimension $\mathrm{Gdim}(C) \in \mathbb{N} \cup \{\infty\}$ is the supremum of the sizes of finite G-shattered sets. Equivalently, $\mathrm{Gdim}(C)$ is the VC dimension of the binary class $\{(x, y) \mapsto [c(x) = y] : c \in C\}$ on $X \times \beta$; for $\beta = \{0,1\}$ it is the VC dimension of $C$.

## Depends on

- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Sources

- B. K. Natarajan, "On Learning Sets and Functions", Machine Learning, 1989.
- S. Ben-David, N. Cesa-Bianchi, D. Haussler and P. M. Long, "Characterizations of Learnability for Classes of {0, ..., n}-Valued Functions", Journal of Computer and System Sciences, 1995.
