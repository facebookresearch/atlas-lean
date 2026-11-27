# A convex combination of samples stays within their bounds

Let the weights `w_i`, indexed by a finite set `s`, be nonnegative with `∑_{i ∈ s} w_i = 1`, and let
the samples satisfy `lo ≤ y_i ≤ hi` for every `i ∈ s`. Then
`lo ≤ ∑_{i ∈ s} w_i y_i ≤ hi`: the interpolated value stays within the bounds of the samples.
