# Park-Pham fragment lemma

There is an absolute constant $L$ such that the following holds. Let $\mathcal{H}$ be an $\ell$-bounded family on $X$, $|X| = n$, and let $W$ be a uniformly random subset of size $w$. For each $W$ and each $S \in \mathcal{H}$ choose $T(S, W) = S' \setminus W$ where $S' \in \mathcal{H}$, $S' \subseteq S \cup W$ minimizes $|S' \setminus W|$ (a *minimum fragment*). Let $\mathcal{T}(W) = \{T(S, W) : S \in \mathcal{H},\ |T(S,W)| \ge k\}$ be the family of large minimum fragments and $p = w/(Ln)$. Then

$$
\mathbb{E}_W \Big[\sum_{T \in \mathcal{T}(W)} p^{|T|}\Big] \le L^{-k},
$$

so by Markov's inequality, with probability at least $1 - 2L^{-k}$ the family of large minimum fragments is $p$-small.

## Proof sketch

Encode a pair $(W, T)$ with $T$ a large minimum fragment by $W \cup T$ (a set of size about $w + |T|$), together with the identity of $T$ inside $W \cup T$, specified using the minimality of $T$ and a member of $\mathcal{H}$ via at most $\ell$-bounded choices. Counting such encodings and comparing with $\binom{n}{w}$ shows that the $p$-weighted number of large fragments is exponentially small in $k$.

## Depends on

- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)
- [Spread lemma: random sets of moderate density contain members of spread families](../../extremal-set-theory/spread-families-and-robust-sunflowers/spread-lemma-random-sets-contain-members-of-spread-families.md)

## Proof depends on

- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)
- [Spread lemma: random sets of moderate density contain members of spread families](../../extremal-set-theory/spread-families-and-robust-sunflowers/spread-lemma-random-sets-contain-members-of-spread-families.md)

## Sources

- Jinyoung Park, Huy Tuan Pham, "A proof of the Kahn-Kalai conjecture", Journal of the AMS 37(1) (2024); arXiv:2203.17207.
