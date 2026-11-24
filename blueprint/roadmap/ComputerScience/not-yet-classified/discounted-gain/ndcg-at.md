# Ndcg At

Normalized discounted cumulative gain at cutoff `k`.

This is `dcgAt` divided by `idealDCGAt` for the bundled valid discounts and
bundled sorted ranking. The selected convention when the ideal DCG is zero
is `0`.
