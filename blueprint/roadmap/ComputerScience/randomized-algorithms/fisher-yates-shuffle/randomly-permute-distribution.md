# Output distribution of the Fisher–Yates shuffle

For a vector $x$ of length $n$, this is
the probability distribution on outcomes (a vector of length $n$ together with a cost pair in
$\mathbb{N} \times \mathbb{N}$) obtained by choosing a draw history $d$ uniformly at random among
all assignments of a number $d_i$ with $0 \le d_i < n - i$ to each position $i < n$, and returning
the result of the Fisher–Yates computation on $x$ and $d$.

This models an ideal source of random draws, not an executable pseudorandom generator, and does
not assume that the output permutation is uniform.
