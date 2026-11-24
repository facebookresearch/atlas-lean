# Correctness of the quadratic LIS program

For every list $xs$ over a preorder, the list
returned by the quadratic longest-increasing-subsequence program on $xs$ is a subsequence of $xs$,
is strictly increasing (each element strictly less than every later one), and is at least as long
as every strictly increasing subsequence of $xs$.
