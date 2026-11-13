# Increasing Paths

The strictly increasing lists of nodes from `j` to `i`: for each subset `S` of the interval
`[j, i]` containing `j` and `i`, the list of the elements of `S` in increasing order. When `B`
is strictly lower triangular every directed path from `j` to `i` is one of these lists
(`mem_increasingPaths_of_isChain`), and a list here that is not a directed path has weight `0`
(`isChain_of_mem_increasingPaths`).
