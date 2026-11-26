# Park-Pham theorem: thresholds are within a logarithmic factor of expectation thresholds

There is a universal constant $K$ such that for every finite set $X$ and every nontrivial increasing family $\mathcal{F} \subseteq 2^X$,

$$
p_c(\mathcal{F}) \le K\, q(\mathcal{F}) \log \ell(\mathcal{F}) .
$$

That is, the Kahn-Kalai expectation-threshold conjecture holds.

## Proof sketch

Let $p = q(\mathcal{F})$ and work with the minimal members $\mathcal{H}$ of $\mathcal{F}$, which is not $2p$-small. Expose $W$ in $O(\log \ell)$ independent rounds, each a random set of density $Lp$. After each round the remaining fragments of every member shrink: by the fragment lemma, with high probability, the family of minimum fragments of size at least half the current size is $p$-small, which together with the non-smallness of $\mathcal{H}$ forces fragments to halve. After $\log_2 \ell$ rounds some member is entirely contained in the union, which has density $O(p\log\ell)$, so $\mu_{Kp\log\ell}(\mathcal{F}) \ge 1/2$.

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
