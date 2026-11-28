# When minimizers can reach density O(1/w)

Use the setting of minimizers $(w, k, O)$ over an alphabet of fixed size $\sigma \ge 2$, with density and charged contexts as in [Density of random minimizers via charged contexts](random-minimizer-density-and-charged-contexts.md). Every window of $w$ consecutive $k$-mers contains a selected position, so no scheme has density below roughly $1/w$; a family of minimizers (with $k = k(w)$) is **asymptotically optimal** if its density is $O(1/w)$ as $w \to \infty$.

**Theorem (threshold on $k$).**

1. If $k \ge \log_\sigma w - c$ for some constant $c$ and all large $w$, the lexicographic minimizer has density $O(1/w)$.
2. If $\log_\sigma w - k \to \infty$, then no minimizer, for any order $O$, has density $O(1/w)$.

Asymptotically, then, the order matters only through constants: the lexicographic order, which performs poorly in practice, already attains the optimal rate whenever any order does.

A set $U \subseteq \Sigma^k$ is a **universal hitting set** (UHS) with path length $w$ if every string of $w$ consecutive $k$-mers contains a $k$-mer of $U$; its relative size is $|U|/\sigma^k$. Every UHS over $k$-mers has relative size at least $1/k - o(1/k)$ (Mykkeltveit's bound on minimal decycling sets of the de Bruijn graph).

**Theorem (charged contexts form a UHS).** For any minimizer $(w, k, O)$, the set of charged contexts, viewed as a set of $(w+k)$-mers, is a UHS over $(w+k)$-mers with path length $w$, and its relative size equals the density of the minimizer.

Consequently any construction of low-density minimizers yields compact universal hitting sets, and the random-minimizer density $2/(w+1) + o(1/w)$ gives UHS of relative size within a constant factor of optimal.

## Depends on

- [Density of random minimizers via charged contexts](random-minimizer-density-and-charged-contexts.md)

## Expansion

*Necessity.* Let $y$ be the $O$-smallest $k$-mer. Any context whose first $k$-mer is $y$ is charged (the first window picks its first position), and such contexts make up a fraction $\sigma^{-k}$ of all contexts. So the density is at least $\sigma^{-k}$, and $w\sigma^{-k} = \sigma^{\log_\sigma w - k} \to \infty$ shows the density is not $O(1/w)$.

*Sufficiency.* For the lexicographic order and $k = \lfloor \log_\sigma (w/2) \rfloor - 2$, a context is charged only if its first window picks position $0$ or its last window picks its last $k$-mer. Windows picking position $0$ start with a long run of zeros relative to everything later in the window; partitioning them by the length of the leading zero run and using that a random string of length $\ell$ avoids $0^d$ with probability at most $3(1 - \sigma^{-(d+1)})^{\ell}$ bounds their number by $O(\sigma^{w})$, a fraction $O(\sigma^{1-k}) = O(1/w)$ of all windows; the last-position case is symmetric. Separate lemmas extend this from that particular $k$ to all $k \ge \log_\sigma w - c$.

*UHS.* Every path of $w$ consecutive $(w+k)$-mers in a long string spans $w$ consecutive contexts, and within any $w$ consecutive contexts some new $k$-mer must be selected, so one of them is charged; counting over a de Bruijn sequence of order $w + k$ shows the relative size equals the density.

## Sources

- H. Zheng, C. Kingsford and G. Marçais, "Improved design and analysis of practical minimizers", Bioinformatics 36 (Suppl. 1) (2020), Section 2.1 (Definition 5, Lemma 2), Section 2.2 (Lemmas 4–5, Theorem 2) and Section 2.3.2 (Theorem 4), <https://doi.org/10.1093/bioinformatics/btaa472> (PMC8248892).
