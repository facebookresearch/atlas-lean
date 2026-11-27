# Probability that two gene copies are copies of the same parental gene

For a parent map
`parent : Fin (2 * N) → Fin N`, let each gene copy $c$ of the offspring generation carry one of
its parent's two genes, the gene $(\mathrm{parent}(c), s(c))$ with $s(c) \in \{0, 1\}$, the choice
map $s$ being uniform over all $2^{2N}$ maps (independent fair choices). This is the probability,
for $s$ uniform and an independent ordered pair $(a, b)$ of distinct gene copies uniform among the
$2N(2N - 1)$ such pairs, that $a$ and $b$ are copies of the same parental gene,
$(\mathrm{parent}(a), s(a)) = (\mathrm{parent}(b), s(b))$. It is $0$ when $N = 0$, as there is
no such pair.
