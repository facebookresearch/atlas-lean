# Density of minimizers ordered by a universal hitting set

Let $G_k$ be the de Bruijn graph of order $k$ over an alphabet of size $\sigma$ (vertices are $k$-mers, edges are $(k+1)$-mers). A *universal hitting set* $U_{k,w}$ is a set of $k$-mers such that every string of length $w+k-1$, equivalently every walk of $w$ vertices in $G_k$, contains an element of $U_{k,w}$. The order $<_{U}$ puts every element of $U_{k,w}$ before every $k$-mer outside it (lexicographic order inside each part), so the minimizer of any window of $w$ consecutive $k$-mers lies in $U_{k,w}$. The *sparsity* $SP(U_{k,w})$ is the proportion of windows of $w+1$ consecutive $k$-mers that contain exactly one element of $U_{k,w}$.

**Theorem.** Assume that whenever a window of $w+1$ consecutive $k$-mers contains $j \ge 1$ elements of $U_{k,w}$, each of them is equally likely to be the smallest. Then the minimizer scheme with order $<_U$ has density factor

$$df = 2\bigl(1 - SP(U_{k,w})\bigr). \tag{3}$$

**Existence of sparse sets.** Let $C = (c_0, \dots, c_{\ell-1})$ be a simple cycle of length $\ell > 3$ in $G_{k-1}$. Its edges form a chordless cycle $C' = (c_0', \dots, c_{\ell-1}')$ in $G_k$. For $w \le 2(\ell-1)$ the set

$$U_{k,w} = \bigl(V(G_k) \setminus C'\bigr) \cup \{c_i' : w \mid i\}$$

is a universal hitting set with $SP(U_{k,w}) > 0$. Taking $C$ to be a Hamiltonian cycle of $G_{k-1}$ gives, for every $k$ and every $w \le 2(\sigma^{k-1}-1)$, a universal hitting set with positive sparsity; under the Theorem's equal-likelihood assumption, the minimizer scheme ordered by it has density factor strictly below $2$ by (3).

## Depends on

- [Expected density of random-order minimizers](../../../../ComputerScience/string-algorithms/winnowing-and-minimizers/winnowing-minimizer-density-2-w-1-and-the-1-5-w-1-lower-bound-for-loca.md)

## Expansion

Call window $W_i$ *charged* if it selects a different position from $W_{i-1}$, and let $Y_{i,j}$ be the event that $W_i$ is charged given that the merged window $W_i' = (m_{i-1}, \dots, m_{i+w-1})$ contains exactly $j$ elements of $U_{k,w}$. Conditioning on whether the two end $k$-mers $m_{i-1}$ and $m_{i+w-1}$ lie in $U_{k,w}$, and placing the remaining elements among the $w-1$ interior positions, gives for $2 \le j \le w+1$

$$\mathbb P[Y_{i,j}] = \frac{2\left[\binom{w-1}{j-1} + \binom{w-1}{j-2}\right]}{j\binom{w+1}{j}} = \frac{2\binom{w}{j-1}}{j\binom{w+1}{j}} = \frac{2}{w+1}$$

For $j = 1$ the single hitting $k$-mer cannot sit at either end, since that would leave $w$ consecutive $k$-mers with no element of $U_{k,w}$, so the window is never charged. Summing over $j$ gives $\mathbb P[W_i \text{ charged}] = 2(1 - SP)/(w+1)$. In the existence construction, a chord $(c_i', c_j')$ with $j \ne i+1$ would force $c_{i+1} = c_j$ in $G_{k-1}$, contradicting simplicity; so the nodes of $C'$ outside $U_{k,w}$ form only paths of fewer than $w$ vertices, and each window starting at an index not divisible by $w$ meets $U_{k,w}$ once. Practical, much smaller sparse sets (built by a heuristic) reach density factors below $1.8$.

## Sources

- G. Marçais, D. Pellow, D. Bork, Y. Orenstein, R. Shamir, C. Kingsford, "Improving the performance of minimizers and winnowing schemes", *Bioinformatics* (2017), Section 2 (Hypothesis 2, Definition 2, Theorem 3 and Theorem 5), Section 3.3, Section 3.4 (Eqs. (6)–(10)) and Section 3.5, <https://doi.org/10.1093/bioinformatics/btx235> (PMC5870760).
