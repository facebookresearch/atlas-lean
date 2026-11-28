# Charged contexts and the energy of a random minimizer

**Minimizers.** Fix a string $S$ over an alphabet of size $\sigma$, a $k$-mer length $k$, a window size $w$, and a total order $O$ on $\Sigma^k$. A window is a substring of length $w + k - 1$ (exactly $w$ consecutive $k$-mers); the $(w, k, O)$ minimizer selects in each window the position of its smallest $k$-mer under $O$, ties broken by the leftmost occurrence. The specific density on $S$ is the number of distinct selected positions divided by $|S|$. A random minimizer uses a uniformly random order.

**Charged contexts.** A context is a substring of length $w + k$, i.e. $w + 1$ consecutive $k$-mers, i.e. two consecutive windows. It is charged if the minimizer selects different positions in its two windows.

**Lemma (counting by contexts).** For any sequence and minimizer, the number of selected positions equals the number of charged contexts plus $1$.

**Energy.** The energy $E(c)$ of a context $c$ is the probability that $c$ is charged under a random minimizer. With $u(c)$ the number of distinct $k$-mers in $c$,

$$E(c) = \begin{cases} 2/u(c) & \text{if the last } k\text{-mer of } c \text{ occurs only once in } c,\\ 1/u(c) & \text{otherwise.}\end{cases}$$

Consequently the expected number of positions a random minimizer selects in $S$ is $1 + E_0(S)$ with initial energy $E_0(S) = \sum_c E(c)$. When all $w + 1$ $k$-mers of every context are distinct, $E(c) = 2/(w+1)$ (the baseline) and the density is $2/(w+1)$.

**Savers and spenders.** A context is an energy saver if $E(c) < 2/(w+1)$ and a spender if $E(c) > 2/(w+1)$; the deficit and surplus of $S$ are

$$D(S) = \sum_c \max\Bigl(0, \tfrac{2}{w+1} - E(c)\Bigr), \qquad X(S) = \sum_c \max\Bigl(0, E(c) - \tfrac{2}{w+1}\Bigr).$$

A uniformly random context is a saver with probability at most $w\sigma^{-k}$ and a spender with probability at most $w(w+1)\sigma^{-k}/2$.

## Expansion

Scanning windows left to right, the selected position changes exactly at charged contexts, and the first window contributes one selection, giving the counting lemma. For the energy, the context is charged exactly when the smallest $k$-mer value of the context sits at its first position (it then leaves the second window) or occurs only at its last position (it then enters only the second window); each event has probability $1/u(c)$ under a random order, and the second is impossible if the last $k$-mer value also occurs earlier, since both windows would then pick the same earlier occurrence. Summing over contexts and using linearity of expectation gives $1 + E_0(S)$. A saver needs a repeated last $k$-mer together with more than $(w+1)/2$ distinct $k$-mers, which is rare when $\sigma^k \gg w$; the probability bounds follow from union bounds over pairs of positions, each pair coinciding with probability $\sigma^{-k}$.

## Sources

- H. Zheng, C. Kingsford, G. Marçais, "Sequence-specific minimizers via polar sets", Bioinformatics 37 (Supplement 1) (2021) i187–i195, Section 2.2.3 (Definitions 4–6, Lemmas 2–6), <https://doi.org/10.1093/bioinformatics/btab313> (PMC8686682).
