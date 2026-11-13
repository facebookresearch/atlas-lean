# The Kadane / Lindley recursion

Appending a score, the maximal segment score is the larger
of the old one and the new value of the reflected walk. So `Mₙ = max_{k ≤ n} W_k`.
