# Universal sets and asymptotically optimal minimizer density

Let $\Sigma$ be an alphabet of size $\sigma \ge 2$ and fix integers $k, w \ge 1$. A **window** is a string $\omega \in \Sigma^{w+k-1}$, viewed as $w$ consecutive $k$-mers. A **local scheme** is a map $f : \Sigma^{w+k-1} \to \{0, \dots, w-1\}$ choosing one $k$-mer per window. A **minimizers scheme** is the local scheme induced by a total order on $\Sigma^k$: $f(\omega)$ is the left-most position of the smallest $k$-mer of $\omega$. For a circular string $S$, the set of selected positions is $\{ i + f(S[i, w+k-1]) : 0 \le i < |S| \}$, and the **density** $d_{f,k,w}$ is the expected fraction of selected positions on an infinitely long i.i.d. uniform sequence. Trivially $1/w \le d_{f,k,w} \le 1$.

A **universal set** $U \subseteq \Sigma^k$ is a set of nodes of the de Bruijn graph $D_{k,\sigma}$ meeting every path of $w$ nodes; equivalently every string of length $w+k-1$ contains a $k$-mer of $U$. A minimizers order is **compatible** with $U$ if every $k$-mer of $U$ is smaller than every $k$-mer outside $U$. Write $\beta_w(D_{k,\sigma})$ for the minimum size of a universal set.

**Lemma.** If $f_U$ is a minimizers scheme compatible with a universal set $U$, then

$$d_{f_U,k,w} \le \frac{|U|}{\sigma^k}.$$

**Corollary.** $\beta_w(D_{k,\sigma}) \ge \sigma^k / w$.

**Theorem (asymptotic optimality in $k$).** If $\sigma$ is even and $w$ is fixed, there is a sequence of universal sets $U_k \subseteq \Sigma^k$ with $|U_k|/\sigma^k \to 1/w$ as $k \to \infty$, and hence a sequence of minimizers schemes $f_k$ with $d_{f_k,k,w} \to 1/w$, the trivial lower bound.

## Expansion

The density equals the particular density on a de Bruijn sequence $S_\ell$ of large enough order $\ell$, in which every $k$-mer occurs exactly $\sigma^{\ell-k}$ times. Because every window contains an element of $U$ and the order ranks $U$ first, every selected $k$-mer lies in $U$, so at most $|U|\,\sigma^{\ell-k}$ of the $\sigma^\ell$ positions are selected; this is the lemma. Combining it with $d \ge 1/w$ gives the corollary. For the theorem, the binary de Bruijn graph is embedded in a $w$-dimensional hypercube so that the $k$-mers falling in a chosen region form a universal set whose relative size tends to $1/w$ (the boundary "slabs" are asymptotically negligible); this generalizes Lichiardopol's asymptotically minimum vertex covers ($w = 2$). An even alphabet is reduced to the binary case by a map $\Sigma \to \{0,1\}$ with equal-size fibres, which preserves relative sizes. The construction gives the first minimizer orders with density factor $d\,(w+1)$ below the previously conjectured $1.5 + 1/(2w)$.

## Sources

- G. Marçais, D. DeBlasio, C. Kingsford, "Asymptotically optimal minimizers schemes", Bioinformatics 34(13) (2018) i13–i22, Section 2.1 (definitions), Lemma 1, Proposition 1 and Theorem 1 (with Propositions 3–4 for the binary construction), <https://doi.org/10.1093/bioinformatics/bty258>, PMCID PMC6037127.
