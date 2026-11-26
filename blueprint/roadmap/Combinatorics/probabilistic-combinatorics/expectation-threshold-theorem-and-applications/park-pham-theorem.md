# Park-Pham theorem: thresholds are within a logarithmic factor of expectation thresholds

There is a universal constant $K$ such that for every finite set $X$ and every nontrivial increasing family $\mathcal{F} \subseteq 2^X$ with $\ell(\mathcal{F}) \ge 2$,

$$
p_c(\mathcal{F}) \le K\, q(\mathcal{F}) \log \ell(\mathcal{F}) .
$$

That is, the Kahn-Kalai expectation-threshold conjecture holds.

## Proof sketch

Fix $p > q(\mathcal{F})$, so that the family $\mathcal{H}$ of minimal members of $\mathcal{F}$ is $\ell$-bounded and not $p$-small; it suffices to work with $\ell$ replaced by $C\ell(\mathcal{F})$ for a large constant $C$. Set $\ell_i = 0.9^i \ell$ and run $\gamma = \lfloor \log_{0.9}(1/\ell) \rfloor + 1$ rounds, so that $\ell_\gamma < 1$. In round $i$ expose a uniformly random subset $W_i$ of the unused ground set of size $L_i p n$, where $L_i = L$ except in the last $\sqrt{\log_{0.9}(1/\ell)}$ rounds, where $L_i = L\sqrt{\log \ell}$, and apply the fragment lemma to the $\ell_{i-1}$-bounded family $\mathcal{H}_{i-1}$ (with $\mathcal{H}_0 = \mathcal{H}$). The exceptional subfamily $\mathcal{G}_i$ of members whose minimum fragment has size at least $0.9\ell_{i-1}$ is set aside together with its cover $\mathcal{U}_i$; the smaller fragments form the $\ell_i$-bounded family $\mathcal{H}_i$, and $W_1 \cup \dots \cup W_i \cup S_i$ lies in $\mathcal{F}$ for every $S_i \in \mathcal{H}_i$. The lemma does not make every fragment shrink; it only makes the discarded part cheap. Since $\ell_\gamma < 1$, either $\mathcal{H}_\gamma = \emptyset$, in which case $\bigcup_i \mathcal{U}_i$ covers $\mathcal{H}$, or $\mathcal{H}_\gamma = \{\emptyset\}$, in which case $W = \bigcup_i W_i \in \mathcal{F}$. Summing the lemma over the rounds bounds the expected cost of $\bigcup_i \mathcal{U}_i$ by $(\log \ell)^{-c}$; as $\mathcal{H}$ is not $p$-small, a cover has cost greater than $1/2$, so by Markov's inequality the first case has probability $o_{\ell \to \infty}(1)$. Thus a uniformly random set of size $O(p \log \ell)\, n$ lies in $\mathcal{F}$ with probability $1 - o(1)$, and a concentration bound transfers this to $\mu_{Kp\log\ell(\mathcal{F})}(\mathcal{F}) > 1/2$.

## Depends on

- [The Kahn-Kalai expectation-threshold conjecture](kahn-kalai-expectation-threshold-conjecture.md)
- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)
- [The threshold $p_c(\mathcal F)$](../thresholds-and-expectation-thresholds/p-c.md)
- [Size of a largest minimal element, $\ell(\mathcal F)$](../thresholds-and-expectation-thresholds/l.md)

## Proof depends on

- [Park-Pham fragment lemma](park-pham-fragment-lemma.md)
- [The expectation threshold is a lower bound on the threshold](expectation-threshold-lower-bounds-the-threshold.md)
- [Thresholds versus fractional expectation-thresholds](../thresholds-and-expectation-thresholds/theorem-1-1.md)

## Sources

- Jinyoung Park, Huy Tuan Pham, "A proof of the Kahn-Kalai conjecture", Journal of the AMS 37(1) (2024); arXiv:2203.17207.
