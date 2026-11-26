# Polar sets and the link-energy density bound

Let $S$, $w$, $k$, the energy $E_0(S)$, deficit $D(S)$ and surplus $X(S)$ be as for random minimizers.

**Polar set.** For slackness $0 \le s < \tfrac12$, a polar set $A$ is a set of $k$-mers such that any two occurrences in $S$ of $k$-mers of $A$ are at least $(1 - s)w$ positions apart. (With $s = 0$, $A$ hits every $w$ consecutive $k$-mers at most once; a universal hitting set hits each at least once.) An order is compatible with $A$ if every $k$-mer of $A$ precedes every $k$-mer outside $A$.

**Link energy.** Two occurrences of $A$-$k$-mers at distance $l \le w$ form a link of energy $2l/(w+1) - 1 \ge 0$. Because occurrences are more than $w/2$ apart, only consecutive occurrences can be linked. The total link energy $L(S, A)$ is the sum over links.

**Theorem.** For a minimizer whose order is compatible with $A$, arbitrary within $A$ and uniformly random outside $A$, the expected number of selected positions in $S$ satisfies

$$1 + E_0(S) - X(S) - L(S, A) \;\le\; \mathbb{E}[\#\text{selected}] \;\le\; 1 + E_0(S) + D(S) - L(S, A).$$

Since $D(S)$ and $X(S)$ are negligible for most sequences, $L(S, A)$ is almost exactly the reduction in selected positions relative to a random minimizer; with $s = 0$ each link contributes $1 - 2/(w+1) \approx 1$.

**Perfect minimizers on short random sequences.** If $S$ is uniformly random with $|S| < \epsilon w \sigma^k / 2$, then with probability at least $1 - \epsilon$ the $k$-mers at every $w$-th position form a set whose compatible minimizers have density exactly $1/w$.

## Depends on

- [Charged contexts and the energy of a random minimizer](charged-contexts-and-the-energy-of-a-random-minimizer.md)

## Expansion

Upper bound: raise every saver context to baseline energy, which adds $D(S)$. Contexts without $A$-$k$-mers have the same charging probability as before. Group the remaining contexts into maximal segments containing $A$-occurrences. A segment with one occurrence has $w + 1$ contexts, baseline total at least $2$, and exactly $2$ charged contexts under $A$. A segment with $d \ge 2$ linked occurrences has $n$ contexts and exactly $d + 1$ charged contexts regardless of the order within $A$ (each $A$-occurrence is the sole $A$-$k$-mer of some window and is selected, and the last context of the segment selects a new non-$A$ $k$-mer); writing $n$ in terms of the distances between consecutive occurrences shows that the baseline total $2n/(w+1)$ exceeds $d + 1$ by exactly the segment's link energy. The lower bound is the same argument with spenders lowered to baseline at cost $X(S)$. The slackness condition $s < \tfrac12$ is what makes every $A$-occurrence the unique $A$-$k$-mer of some window. The perfect-minimizer statement is a union bound over the $|S|^2/w$ pairs of selected and unselected positions. Choosing a polar set of maximum link energy is NP-hard, so heuristics build layered polar sets greedily on the reference.

## Sources

- H. Zheng, C. Kingsford, G. Marçais, "Sequence-specific minimizers via polar sets", Bioinformatics 37 (Supplement 1) (2021) i187–i195, Sections 2.1–2.2 (Definitions 1–3, Lemma 1, Theorem 1 and its proof), <https://doi.org/10.1093/bioinformatics/btab313> (PMC8686682).
