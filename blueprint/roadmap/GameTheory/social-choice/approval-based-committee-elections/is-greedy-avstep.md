# Is Greedy AVStep

One GreedyAV round from the committee `W`: the chosen candidate `c ∉ W` maximizes `s_W` over
the candidates outside `W`. The ballots still in the source's `A'` are those disjoint from `W`,
so a candidate's approval score with respect to `A'` is `s_W`. Once no remaining ballot approves
a candidate outside `W`, every such candidate has `s_W = 0`, so this round also covers the
source's arbitrary completion.
