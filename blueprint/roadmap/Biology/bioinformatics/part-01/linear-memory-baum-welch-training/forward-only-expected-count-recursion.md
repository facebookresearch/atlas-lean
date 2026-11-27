# Forward-only expected-count recursion

**Baum–Welch update.** Consider an HMM with $M$ states including silent Start and End, transition probabilities $T_{i,j}$ and emission probabilities $E_i(y)$, and a training set $\mathcal S$ of sequences $X = x_1 \cdots x_L$. With forward probabilities $f(X_k, i) = P(x_1, \dots, x_k, s(x_k) = i)$ and backward probabilities $b(X_k, i) = P(x_{k+1}, \dots, x_L \mid s(x_k) = i)$, one EM iteration sets

$$T^{\mathrm{new}}_{i,j} = \frac{\sum_{X \in \mathcal S} t_{i,j}(X)/P(X)}{\sum_{j'}\sum_{X \in \mathcal S} t_{i,j'}(X)/P(X)}, \qquad t_{i,j}(X) = \sum_{k} f(X_k, i)\, T_{i,j}\, E_j(x_{k+1})\, b(X_{k+1}, j),$$

and analogously for emissions. Here $t_{i,j}(X)$ equals the sum over all state paths of their probability times their number of $i \to j$ transitions.

**Theorem.** Define $t_{i,j}(X_k, l)$ as the weighted sum, over state paths for $x_1 \cdots x_k$ ending in state $l$ at position $k$, of path probability times number of $i\to j$ transitions. Initialize $f(X_0, m) = [m = \mathrm{Start}]$ and $t_{i,j}(X_0, m) = 0$, and recurse

$$f(X_{k+1}, m) = \sum_{n=1}^M f(X_k, n)\, T_{n,m}\, E_m(x_{k+1}),$$

$$t_{i,j}(X_{k+1}, m) = \sum_{n=1}^M t_{i,j}(X_k, n)\, T_{n,m}\, E_m(x_{k+1}) + [m = j]\, f(X_k, i)\, T_{i,j}\, E_j(x_{k+1}),$$

finishing with $P(X) = \sum_n f(X_L, n) T_{n,\mathrm{End}}$ and $t_{i,j}(X) = \sum_n t_{i,j}(X_L, n)\, T_{n,\mathrm{End}} + [j = \mathrm{End}]\, f(X_L, i)\, T_{i,\mathrm{End}}$. This computes $t_{i,j}(X)$ in $O(M)$ memory and $O(L M T_{\max})$ time, where $T_{\max}$ is the maximum number of states any state connects to.

**Corollary.** Running the recursion for all $T$ free transition and $E$ free emission parameters gives one Baum–Welch iteration in $O(M)$ memory and $O(LMT_{\max}(T+E))$ time, versus $O(M \log L)$ memory for checkpointing. For an $n$-dimensional HMM (e.g. a pair HMM, $n=2$) on sequences of length $L$, memory drops from $O(\log(L) L^{n-1} M)$ to $O(L^{n-1}M)$, and running $c$ parameters' recursions in parallel trades time $L^n M T_{\max} c$ against memory $L^{n-1} M (T + E - c)$.

## Depends on

- [Forward value of a sequence under a profile HMM](../../sequence-alignment/profile-hidden-markov-models/forward.md)

## Expansion

The proof is induction on $k$: a path ending in $m$ at position $k+1$ either extends a path ending in some $n$ at position $k$ without adding an $i \to j$ step (first term, carrying over its count), or, when $m = j$ and the last step is $i \to j$, gains one extra count, contributing that path's plain probability $f(X_k, i)T_{i,j}E_j(x_{k+1})$ once. Only one slice of $f$ and $t_{i,j}$ values per position is kept, so no backward pass, recursion or checkpointing is needed; the cost is one extra forward-sized scan per free parameter. Emission counts satisfy the same recursion with the indicator moved to emissions of letter $y$ in state $i$.

## Sources

- I. Miklós, I. M. Meyer, "A linear memory algorithm for Baum-Welch training", BMC Bioinformatics 6:231 (2005), Eqs 1–4 and Theorem 1, <https://doi.org/10.1186/1471-2105-6-231>, PMCID PMC1262623.
