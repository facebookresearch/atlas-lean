# Unimodal rearrangement algorithm

Given an array `arr` which is a permutation of the numbers from `1` to `arr.size`,
`minRearrange` computes the size of the smallest subset of indices within the array
that may be permuted such that the array becomes first increasing and then decreasing.
For example, `minRearrange #[1, 6, 4, 3, 2, 5] = 2` since we can swap the first and
the last element to achieve the desired property.

A candidate for a preserved position is the midpoint of an edge that places the original
value there. After sorting these points lexicographically, the algorithm subtracts the length
of a longest nondecreasing subsequence of their second coordinates from the array length.
The implementation runs in `O(n log n)`.

* `minRearrange #[] = 0`
* `minRearrange #[1, 6, 4, 3, 2, 5] = 2`
* `minRearrange #[4, 3, 2, 1, 5] = 4`
* `minRearrange #[1, 2, 4, 3] = 0`
* `minRearrange #[1, 2, 7, 4, 5, 6, 3, 8, 9, 10] = 2`
