# Reversals characterize the nonzero elements of $\bar E^\ast$

Let $L$ be a list of natural
numbers of length at least $2$ with nonzero first entry, let $E$ be the periodic Zeckendorf
collection determined by $L$, and let $\bar E^*$ be the closure of the collection $E^*$ determined
by $L$. For $n \in \mathbb N$ and a coefficient function $\varepsilon : \mathbb N \to \mathbb N$,
let $\mathrm{rev}_n(\varepsilon)$ be the finitely supported coefficient function whose first $n$
entries are the first $n$ entries of $\varepsilon$ in reverse order and whose other entries are
$0$. Then a nonzero coefficient function $\varepsilon : \mathbb N \to \mathbb N$ satisfies
$\mathrm{rev}_n(\varepsilon) \in E$ for every $n \in \mathbb N$ if and only if
$\varepsilon \in \bar E^*$.

This reads the source's Lemma 3 for nonzero $\varepsilon$ and counts $\bar\beta^1$, the maximal
$L^*$-block starting at the first index, as an element of $\bar E^*$. As printed (no
$\varepsilon \ne 0$, decompositions with at least one block) the lemma fails at
$\varepsilon = 0$, since $\mathrm{rev}_n(0) = 0 \in E$, and at $\varepsilon = \bar\beta^1$,
since $\mathrm{rev}_n(\bar\beta^1)$ is the maximal $L$-block $\theta^{n+1}$, which lies in $E$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Lemma 3 (`integers-2025-A25-lem-3`).
