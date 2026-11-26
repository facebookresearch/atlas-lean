# Multicalibration yields the hard-core lemma with optimal density

Let $g : \{0,1\}^n \to \{0,1\}$ be $\delta$-hard for circuits of size $s$ under a distribution $\mu$, meaning every circuit of size $s$ disagrees with $g$ on at least a $\delta$ fraction of inputs. Then for every $\varepsilon > 0$ there is a distribution $H$ of density at least $2\delta$ in $\mu$ (that is, $H \le \mu/(2\delta)$ pointwise) such that $g$ is $(\tfrac12 - \varepsilon)$-hard on $H$ for circuits of size $s' = s\cdot\mathrm{poly}(\varepsilon, \delta)$ (up to the source's exact polynomial loss). The density $2\delta$ is optimal (Holenstein's bound) and is obtained by taking a multicalibrated predictor of $g$ with respect to small circuits and collecting its level sets, reweighted toward the most unpredictable ones.

## Proof sketch

Let $p$ be a low-complexity predictor multicalibrated with respect to circuits of size $s'$. On each level set $\{p = v\}$, $g$ is indistinguishable by small circuits from a $\mathrm{Ber}(v)$ coin, so the best small circuit errs with probability about $\min(v, 1-v)$ there; $\delta$-hardness forces $\mathbb{E}[\min(p, 1-p)] \gtrsim \delta$. Weight each level set by $\min(v,1-v)$ to obtain a distribution of density about $2\delta$ on which the conditional outcome looks like a fair coin to small circuits, which is the hard-core distribution.

## Depends on

- [Multiaccuracy is the Trevisan–Tulsiani–Vadhan regularity lemma](multiaccuracy-regularity-lemma.md)
- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [Multiaccuracy is the Trevisan–Tulsiani–Vadhan regularity lemma](multiaccuracy-regularity-lemma.md)
- [Multicalibrated predictors](multicalibrated-predictor.md)

## Sources

- S. Casacuberta, C. Dwork, S. Vadhan, "Complexity-Theoretic Implications of Multicalibration", STOC (2024), arXiv:2312.17223.
- L. Trevisan, M. Tulsiani, S. Vadhan, "Regularity, Boosting, and Efficiently Simulating Every High-Entropy Distribution", CCC (2009).
