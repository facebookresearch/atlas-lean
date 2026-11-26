# Actual holonomic reconstruction is Iso

For a bounded holonomic object $M$ of the derived category of $\mathcal{D}_X$-modules whose
enhanced solution complex is bounded (`BoundedSolution`): the $\beta$-pullback of
$\mathcal{D}$-modules has a right adjoint (the statement of `ordinary_beta_pull_right_adjoint`),
and, for this right adjoint, the reconstruction map of $M$ built from the enhanced ind-sheaf
$\mathcal{O}^E_X$ of tempered holomorphic functions is an isomorphism (the ringed form of
D'Agnolo--Kashiwara, Theorem 9.5.3). The reconstruction map is formed with the left adjoint of the
enhanced quotient functor (`coefficient_enhanced_quotient_left_adjoint`), the internal Hom right
adjoint to tensoring with a bounded coefficient complex (`bounded_coefficient_tensor_closed`) and
the right adjoint of the $\beta$-pullback.
