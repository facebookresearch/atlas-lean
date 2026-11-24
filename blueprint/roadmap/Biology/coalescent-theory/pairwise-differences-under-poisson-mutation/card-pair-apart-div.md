# Fraction of histories in which two genes are apart after $t$ events

Let `a ≠ b` be genes of a sample of size `n`, and let `t` be a natural number with `t + 2 ≤ n`,
that is, `n ≥ 2` and `t ≤ n - 2`. Among all
[ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes, the
fraction of those in which `a` and `b` are [apart](pair-apart.md) after `t` coalescence events is
`(n - t - 1)(n + 1) / ((n - t + 1)(n - 1))` (Tajima 1983). By the
[counting step](card-pair-apart-succ.md), starting from [all histories](pair-apart-zero.md) at
`t = 0`, it is also the product over the steps `i < t` of `1 - 1 / C(n - i, 2)`. Under
[random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md) every history is
[equally likely](../ranked-labeled-histories-of-coalescent-trees/random-joining-singleton-eq-inv.md),
so this fraction is the probability that `a` and `b` are still in different lineages after `t`
events. With `k = n - t` lineages it is the
[probability that a pair lies in separate lineages](../segregating-sites-and-pairwise-differences/pair-separate-prob.md),
`(k - 1)(n + 1) / ((n - 1)(k + 1))`; the
[random-joining statement](integral-pair-apart-random-joining.md) expresses it in that form.
