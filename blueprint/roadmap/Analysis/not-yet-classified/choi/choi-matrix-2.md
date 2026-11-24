# Choi Matrix

Choi matrix of a completely positive map `φ : Matrix n n ℂ →CP Matrix m m ℂ`.

Thin specialization of `LinearMap.choiMatrix` to the bundled CP type. The
`((i,a),(j,b))` entry is `φ (Matrix.single i j 1) a b`.
