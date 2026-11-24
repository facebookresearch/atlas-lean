# From Choi Matrix

Reconstruction from a Choi matrix by matrix-unit expansion.

For `J : Matrix (n × m) (n × m) ℂ`, the associated linear map sends
`X` to `∑ i j, X i j • (of fun a b => J (i,a) (j,b))`. This is the inverse of
`LinearMap.choiMatrix` under the repository product ordering.
