# Proposal counts in the Gale–Shapley algorithm

Let $P$ be a preference profile for $n$ men
and $n$ women. The number $p_t(i)$ of women man $i$ has proposed to after $t$ rounds of the
men-proposing Gale–Shapley algorithm on $P$ is defined by $p_0(i) = 0$ and, for every $t$,
$p_{t+1}(i) = p_t(i)$ if man $i$ is provisionally engaged in the state $p_t$ and
$p_{t+1}(i) = p_t(i) + 1$ otherwise: in each round every man who is not provisionally engaged
proposes to his next choice.

## Sources

- Borodin et al., *Sequences of the Stable Matching Problem*, Journal of Integer Sequences 27 (2024), Article 24.2.2, Section 2.
