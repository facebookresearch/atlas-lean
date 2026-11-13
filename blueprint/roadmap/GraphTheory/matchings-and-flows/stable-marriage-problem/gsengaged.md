# Provisional engagement in the Gale–Shapley algorithm

Let $P$ be a preference profile for
$n$ men and $n$ women, with positions in each ranking numbered $0, \dots, n - 1$, and consider
the state of the men-proposing Gale–Shapley algorithm in which each man $i'$ has proposed to the
women at the positions $r' < p(i')$ of his ranking. Man $i$ is provisionally engaged in this
state if $1 \le p(i) \le n$ and the woman $w$ at his position $p(i) - 1$ (the last woman he
proposed to) ranks him weakly above every man who has proposed to her: her position for $i$ is
at most her position for every man $i'$ who has $w$ at some position $r' < p(i')$.

## Sources

- Borodin et al., *Sequences of the Stable Matching Problem*, Journal of Integer Sequences 27 (2024), Article 24.2.2, Section 2 (description of the Gale–Shapley algorithm).
