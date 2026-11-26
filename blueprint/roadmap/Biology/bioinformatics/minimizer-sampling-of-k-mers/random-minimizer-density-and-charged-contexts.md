# Density of random minimizers via charged contexts

Let $\Sigma = \{0, 1, \dots, \sigma - 1\}$ be a fixed alphabet with $\sigma \ge 2$. A **minimizer** is a triple $(w, k, O)$ with integers $w, k \ge 1$ and a total order $O$ on $\Sigma^k$. A **window** is a string of length $w + k - 1$, i.e. $w$ overlapping $k$-mers; the minimizer maps a window to the position of its $O$-smallest $k$-mer, ties broken by taking the leftmost one. Given a string $S$, a position is **selected** if it is picked in at least one window of $S$. The **density** of the minimizer is the expected fraction of selected $k$-mer positions in a sufficiently long uniformly random string; the **density factor** is the density multiplied by $w + 1$. With $O$ the dictionary order the scheme is a lexicographic minimizer; with $O$ a uniformly random permutation of $\Sigma^k$ it is a **random minimizer**.

A **context** is a string of length $w + k$, i.e. two consecutive windows (equivalently $w + 1$ consecutive $k$-mers). It is **charged** if the minimizer picks different positions in its first and its last window.

**Lemma (charged contexts).** A context is charged if and only if the minimizer picks the first $k$-mer of the first window or the last $k$-mer of the last window.

Because selections can only move forward, counting selected positions in a string is the same as counting its charged contexts, so the density equals the probability that a uniformly random context $c \in \Sigma^{w+k}$ is charged.

**Theorem (density of random minimizers).** If $k > (3 + \epsilon) \log_\sigma (w + 1)$ for some fixed $\epsilon > 0$, the expected density of a random minimizer, over both the random string and the random order, is

$$\frac{2}{w + 1} + o\!\left(\frac{1}{w}\right) \qquad (w \to \infty).$$

This recovers, without the earlier heuristic independence assumptions on the string, the classical estimate $2/(w+1)$ for winnowing and minimizer schemes.

## Expansion

*Lemma.* If the first or last $k$-mer of the context is picked, it lies in only one of the two windows, so the two picks differ. Otherwise both windows pick a $k$-mer from their common part; if they picked different ones, both picks would lie in both windows and one of them would not be minimal, a contradiction.

*Theorem.* Let $I(c)$ be the event that the $w + 1$ $k$-mers of $c$ are not all distinct. Under the stated growth of $k$, a random context has $P(I(c)) = o(1/w)$. If all $k$-mers are distinct, then under a uniformly random order each of the $w + 1$ $k$-mers is the minimum with probability exactly $1/(w+1)$; by the lemma the context is charged exactly when the minimum is the first or the last $k$-mer, two disjoint events, so $P_O(c \text{ charged} \mid \overline{I(c)}) = 2/(w+1)$. Hence

$$\Big(1 - o(1/w)\Big)\frac{2}{w+1} \le P_{c,O}(c \text{ charged}) \le P(I(c)) + \frac{2}{w+1} = \frac{2}{w+1} + o(1/w).$$

## Sources

- H. Zheng, C. Kingsford and G. Marçais, "Improved design and analysis of practical minimizers", Bioinformatics 36 (Suppl. 1) (2020), Section 2.1 (Definitions 1–4, Lemma 1) and Section 2.3.1 (Theorem 3), <https://doi.org/10.1093/bioinformatics/btaa472> (PMC8248892).
