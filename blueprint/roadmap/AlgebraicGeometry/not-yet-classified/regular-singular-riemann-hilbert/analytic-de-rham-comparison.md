# Analytic de Rham comparison

Let $S \subset \mathbb{C}$ be finite and $A$ an $r \times r$ matrix of rational functions with
poles in $S$ (`hA`). Then there is a quasi-isomorphism $\eta$ from the sheaf of holomorphic
solutions of $f' = Af$ on $\mathbb{C} \setminus S$ (`solutionSheaf`), placed in degree $0$, to the
analytic de Rham complex $\mathcal{O}^r \to \Omega^r$, $f \mapsto f' - Af$, of the de Rham data
`analytic_connection_deRham_data` (unshifted, in degrees $0$ and $1$; its shift by $[1]$ is the
perverse normalization on a curve), such that in degree $0$, $\eta$ sends every solution on an
open $U$ to the same function, viewed as a holomorphic vector function on $U$.
