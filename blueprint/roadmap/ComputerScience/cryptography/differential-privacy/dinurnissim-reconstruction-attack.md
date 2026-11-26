# Dinur–Nissim reconstruction attack

Let $d \in \{0,1\}^n$. If a mechanism's answers to all $2^n$ subset-sum queries always have distortion at most $E$, then the adversary that asks all of them and outputs the first $c \in \{0,1\}^n$, in a fixed order, whose subset sums are all within $E$ of the answers (running in exponential time) outputs a candidate that differs from $d$ in at most $4E$ positions; in particular, a mechanism whose distortion is $o(n)$ is blatantly non-private. If the distortion is $E = o(\sqrt n)$, let the adversary ask $t = n (\log n)^2$ uniformly random subset-sum queries $q_1, \dots, q_t$, solve the linear program $|\sum_{i \in q_j} c_i - \tilde a_{q_j}| \le E$ for $j \le t$ and $0 \le c_i \le 1$ for $i \le n$, and round each $c_i$ to $1$ if $c_i > 1/2$ and to $0$ otherwise. This adversary runs in time polynomial in $n$, each answer of the mechanism counting as one step, and for every $\varepsilon > 0$ its candidate differs from $d$ in fewer than $\varepsilon n$ positions except with probability $\mathrm{neg}(n)$, a function that is smaller than $n^{-k}$ for all large $n$, for every $k$. Consequently, a mechanism against which every adversary running in time polynomial in $n$ fails in this sense has distortion that is not $o(\sqrt n)$.

## Depends on

- [Blatant non-privacy](blatant-non-privacy-and-distortion-of-subset.md)
- [Distortion](has-distortion.md)
- [Subset-sum query](subset-sum-query.md)

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Theorem 8.1
- I. Dinur and K. Nissim, "Revealing information while preserving privacy", *Proceedings of the 22nd ACM PODS*, 2003, pp. 202–210, Definition 3 and Theorems 2 and 3
