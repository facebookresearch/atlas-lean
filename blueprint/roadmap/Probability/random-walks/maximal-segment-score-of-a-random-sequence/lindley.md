# Lindley reflected walk of a score list

For a list of real scores `x₀, …, x_{n-1}`, the Lindley (reflected) walk is `W₀ = 0`,
`W_{k+1} = max(0, W_k + x_k)`, and its value after the whole list is `Wₙ`. By
[Lindley duality](lindley-eq-walk-max-reverse.md), `Wₙ = max_{0 ≤ i ≤ n} (Sₙ - S_i)`, the
[walk maximum](walk-max.md) of the reversed list, where `S_k` are the partial sums.
