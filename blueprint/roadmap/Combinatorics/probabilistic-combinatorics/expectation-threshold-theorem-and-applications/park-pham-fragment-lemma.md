# Park-Pham fragment lemma

There is an absolute constant $L_0$ such that the following holds for every $L \ge L_0$. Let $\ell \ge 1$, let $\mathcal{H}$ be an $\ell$-bounded family on $X$ with $|X| = n$, let $p > 0$ be such that $w = Lpn$ is an integer at most $n$, and let $W$ be a uniformly random $w$-subset of $X$. For $S \in \mathcal{H}$, a *minimum $(S, W)$-fragment* $T(S, W)$ is a smallest set of the form $S' \setminus W$ with $S' \in \mathcal{H}$ and $S' \subseteq S \cup W$ (ties broken arbitrarily). Let

$$
\mathcal{G}(W) = \{S \in \mathcal{H} : |T(S, W)| \ge 0.9\,\ell\}, \qquad \mathcal{U}(W) = \{T(S, W) : S \in \mathcal{G}(W)\}.
$$

Then $\mathcal{U}(W)$ covers $\mathcal{G}(W)$, since $T(S, W) \subseteq S$, and

$$
\mathbb{E}_W \Big[\sum_{U \in \mathcal{U}(W)} p^{|U|}\Big] < L^{-0.8\,\ell} .
$$

By Markov's inequality, with probability greater than $1 - 2L^{-0.8\ell}$ the cover $\mathcal{U}(W)$ of $\mathcal{G}(W)$ has cost $\sum_{U \in \mathcal{U}(W)} p^{|U|} < 1/2$, so $\mathcal{G}(W)$ is $p$-small. The remaining members are handled by their fragments: $\mathcal{H}'(W) = \{T(S, W) : S \in \mathcal{H} \setminus \mathcal{G}(W)\}$ is $0.9\ell$-bounded, and every member of $\mathcal{H} \setminus \mathcal{G}(W)$ contains a member of $\mathcal{H}'(W)$.

## Proof sketch

Fix $m \ge 0.9\ell$ and count the pairs $(W, T(S, W))$ with $|T(S, W)| = m$. First choose $Z = W \cup T$, a set of size $w + m$; there are at most $\binom{n}{w}(Lp)^{-m}$ choices. Then fix a member $\hat S \subseteq Z$ of $\mathcal{H}$ depending only on $Z$ (one exists by the definition of a fragment). Minimality of $T$ forces $T \subseteq \hat S$, so $T$ is one of at most $2^\ell$ subsets of $\hat S$, and $W = Z \setminus T$. Hence the $p$-weighted count is at most $\binom{n}{w} L^{-m} 2^{\ell}$, and summing over $m \ge 0.9\ell$ gives less than $\binom{n}{w} L^{-0.8\ell}$ once $L$ is large.

## Depends on

- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)

## Sources

- Jinyoung Park, Huy Tuan Pham, "A proof of the Kahn-Kalai conjecture", Journal of the AMS 37(1) (2024); arXiv:2203.17207, Section 2.1, Lemma 2.1.
