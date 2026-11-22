# Entropy in nats and entropy in bits

For a probability mass function $p$ on a finite alphabet,
$\sum_a -p(a)\log p(a) = H_2(p)\cdot\log 2$, where $\log$ is the natural logarithm, $0 \log 0 = 0$ and
$H_2(p) = \sum_a -p(a)\log_2 p(a)$ is the Shannon entropy in bits: the natural-log entropy used on this topic
is the base-two entropy times $\log 2$. Csiszár (1998) allows any base, used consistently; Csiszár–Shields
use base 2.

## Background

- [Shannon entropy](../shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md): the entropy there
  is in bits; the natural-log entropy $\sum_a -P(a)\log P(a)$ used here is it times $\log 2$.

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Section II (base of $\log$ and $\exp$ arbitrary but the same).
