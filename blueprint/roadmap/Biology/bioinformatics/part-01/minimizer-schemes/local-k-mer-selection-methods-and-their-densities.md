# Local k-mer selection methods and their densities

**Definitions.** Fix an alphabet $\Sigma$ and $k \ge 1$. A *$k$-mer selection method* $f$ maps each string $S \in \Sigma^*$ to a set of pairs $(x, i)$ with $x = S[i, k]$ a $k$-mer of $S$ starting at position $i$. The method is **$q$-local** if, for every $S$ with $|S| \ge k + q - 1$,

$$f(S) = \bigcup_{i=1}^{|S| - (k+q-1) + 1} f\big(S[i, k+q-1]\big)$$

(positions shifted appropriately): $f$ is determined by its action on $(k+q-1)$-mers. A $1$-local method decides for each $k$-mer in isolation. A local method has the **$r$-window guarantee** if $f(s) \ne \emptyset$ for every $s \in \Sigma^{k+r-1}$, i.e. every $r$ consecutive $k$-mers contain a selected one. The **density** of $f$ is the limiting expected fraction of $k$-mers selected in a uniformly random i.i.d. string as $|S| \to \infty$.

**Locality theorem.** If $f$ is $q$-local and $S[i, k+q-1] = S'[j, k+q-1]$, then every $k$-mer of $f(S[i, k+q-1])$ is selected in both $f(S)$ and $f(S')$. (MinHash sketches and "every $n$-th $k$-mer" rules are not local.)

**Methods.**

- **Minimizer** $(w, k, \mathcal{O})$: with a total order $\mathcal{O}$ on $k$-mers, select in every window of $w$ consecutive $k$-mers the smallest one (ties to the leftmost). This is $w$-local with the $w$-window guarantee. A *random minimizer* uses a uniformly random order.
- **Closed syncmer** $(k, s)$, $s < k$: view a $k$-mer as $k - s + 1$ consecutive $s$-mers; select it if the smallest $s$-mer is the first or the last. It is $1$-local with a $(k-s)$-window guarantee.
- **Open syncmer** $(k, s, t)$, $1 \le t \le k - s + 1$: select a $k$-mer if its smallest $s$-mer is at position $t$. It is $1$-local and in general has no window guarantee (e.g. on $AAAA\cdots$ with $t = 2$ nothing is selected).

**Densities.** Assuming no window of $w + 1$ consecutive $k$-mers contains duplicates, a random minimizer has density $2/(w+1)$. Open and closed syncmers have densities $1/(k-s+1)$ and $2/(k-s+1)$, up to an error $o\big((k-s+1)^2/|\Sigma|^s\big)$ from repeated $s$-mers.

**Uniqueness trade-off.** If a $1$-local method $f_1$ and an $n$-local method $f_n$ ($n > 1$) have equal density, then on a long uniformly random string $f_n$ selects strictly more unique $k$-mers in expectation than $f_1$.

## Expansion

For minimizers, the number of selected $k$-mers equals one plus the number of window shifts at which the selected position changes. Consecutive windows starting at $i$ and $i+1$ select different $k$-mers exactly when the smallest $k$-mer of the combined window of $w + 1$ $k$-mers is its first or last element (a *charged context*); under a random order and no duplicates the minimum is uniform over the $w+1$ positions, so this has probability $2/(w+1)$, which is the density. The same argument with $s$-mers inside a $k$-mer gives the syncmer densities, the minimum of $k - s + 1$ distinct $s$-mers falling at a prescribed position with probability $1/(k-s+1)$. A $1$-local method must select every copy of a chosen $k$-mer wherever it recurs, so repeated $k$-mers are selected as often as unique ones; a method with wider context can decline to pick a repeat in some of its occurrences, which yields the uniqueness advantage.

## Sources

- J. Shaw, Y. W. Yu, "Theory of local k-mer selection with applications to long-read alignment", Bioinformatics 38 (2022) 4659–4669, Section 2 (Definitions 1–7, Theorems 1–2, Table 2) and Section 3.4 (Theorem 5), <https://doi.org/10.1093/bioinformatics/btab790>.
- S. Schleimer, D. S. Wilkerson, A. Aiken, "Winnowing: local algorithms for document fingerprinting", Proceedings of ACM SIGMOD (2003) 76–85, <https://doi.org/10.1145/872757.872770>.
