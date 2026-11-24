# Correctness of patience sorting

For every list $xs$ over a linear order, the value
returned by patience sorting on $xs$ is the length of a longest strictly increasing subsequence of
$xs$: some strictly increasing subsequence of $xs$ has this length, and no strictly increasing
subsequence of $xs$ is longer.
