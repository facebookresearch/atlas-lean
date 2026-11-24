# The Kadane–Lindley recursion

For a list of real scores `l` and a real score `a`, the [maximal segment score](max-seg-score.md)
of `l` followed by `a` is the larger of the maximal segment score of `l` and the value of the
[Lindley reflected walk](lindley.md) after `l` followed by `a`. Hence `Mₙ = max_{k ≤ n} W_k`.
