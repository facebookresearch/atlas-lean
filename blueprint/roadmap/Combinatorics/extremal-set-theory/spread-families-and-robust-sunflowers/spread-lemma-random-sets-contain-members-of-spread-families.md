# Spread lemma: random sets of moderate density contain members of spread families

Let $k \ge 1$ and $r \ge 1$. A sequence $S_1, \dots, S_m$ of $k$-element subsets of a finite set $X$ (repetitions allowed) is **$r$-spread in the absolute sense** if for every nonempty $Z \subseteq X$ at most $r^{k - |Z|}$ indices $i$ satisfy $Z \subseteq S_i$. If moreover $r > 1$ and $m \ge r^k$, then for every nonempty $Z$ the number of such indices is at most $r^{-|Z|} m$, so the sequence, viewed as a multiset, is $r$-spread in the relative sense.

**Uniform random set (Rao, Lemma 4).** There is an absolute constant $\beta > 1$ such that the following holds. Let $\varepsilon, \gamma \in (0, 1/2)$ and $r = \beta\, \gamma^{-1} \log(k/\varepsilon)$. Let $S_1, \dots, S_m$ be a sequence of $k$-element subsets of $X$ that is $r$-spread in the absolute sense, with $m \ge r^k$, and let $W$ be a uniformly random subset of $X$ of a fixed size at least $\gamma |X|$. Then

$$
\Pr\big[\exists i : S_i \subseteq W\big] > 1 - \varepsilon .
$$

**Binomial random set (Bell–Chueluecha–Warnke, Theorem 3).** There is an absolute constant $B \ge 1$ such that the following holds for every integer $k \ge 2$, all reals $\delta, \varepsilon \in (0, 1/2]$ and every $r \ge B\, \delta^{-1} \log(k/\varepsilon)$. Let $\mathcal{S}$ be a family of $k$-element subsets of $X$ that is $r$-spread in the absolute sense, with $|\mathcal{S}| \ge r^k$, and let $X_\delta$ contain each element of $X$ independently with probability $\delta$. Then

$$
\Pr\big[\exists S \in \mathcal{S} : S \subseteq X_\delta\big] > 1 - \varepsilon .
$$

The threshold is best possible up to the constant: for all reals $\delta, \varepsilon \in (0, 1/2]$ and integers $k \ge 1$ and $1 \le r \le 0.25\, \delta^{-1} \ln(k/\varepsilon)$ there is a family of exactly $r^k$ subsets of size $k$ of a set of $rk$ elements, $r$-spread in the absolute sense, for which the probability is less than $1 - \varepsilon$ (Bell–Chueluecha–Warnke, Lemma 4).

## Proof sketch

Rao's encoding argument: for a random index $x$ and the random set $W$, let $\chi(x, W) = S_y \setminus W$ for a $y$ minimizing $|S_y \setminus W|$ among the sets with $S_y \subseteq S_x \cup W$, so that some $S_y$ lies in $W$ exactly when $\chi(x, W) = \emptyset$. Splitting $W$ into many small random pieces and adding them one at a time, the fragment shrinks in expectation at each step: a prefix-free encoding of the pair (index, set) through the fragment would otherwise be shorter on average than the entropy of a uniform choice allows, because spreadness bounds the number of indices consistent with a given fragment. This gives $\mathbb{E}\,|\chi(x, W)| < \varepsilon$. The binomial version follows by conditioning on $|X_\delta| \ge \lceil \delta |X| / 2 \rceil$, which holds with high probability, and applying Rao's argument for uniform random sets of size $\lceil \delta |X| / 2 \rceil$.

## Depends on

- [Spread families and spread measures](kappa-spread-families-and-measures.md)

## Sources

- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774, Lemma 4.
- Tolson Bell, Suchakree Chueluecha, Lutz Warnke, "Note on sunflowers", Discrete Mathematics 344(7) (2021) 112367; arXiv:2009.09327, Theorem 3, Lemma 4 and Appendix.
- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
