# Running time of the closest-pair recursion

For every list of $n$ points in $\mathbb{R}^2$
sorted by nondecreasing $x$-coordinate, the divide-and-conquer recursion of the closest-pair
algorithm computes at most $7 n \lceil \log_2 n \rceil + n$ squared distances, where
$\lceil \log_2 0 \rceil$ is read as $0$.
