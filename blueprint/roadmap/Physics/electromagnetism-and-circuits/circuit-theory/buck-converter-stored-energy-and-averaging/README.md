# Buck converter: stored energy and averaging

## Stored energy of the switched converter

- [Stored energy of the ideal buck converter](buck-stored-energy.md)
- [The buck stored energy is L i² / 2 + C v² / 2](buck-stored-energy-eq.md)
- [The buck stored energy is nonnegative](buck-stored-energy-nonneg.md)
- [Branch voltages of the ideal buck converter](buck-branch-voltage.md)
- [Branch currents of the ideal buck converter](buck-branch-current.md)
- [The capacitor law gives current balance at the output node](output-node-current-balance-of-capacitor.md)
- [Node current balance of the buck network](buck-embedding-current-balance.md)
- [Between switches the buck energy changes at supplied power minus loss](buck-stored-energy-has-deriv-at-eq-suppl.md)
- [Integrated energy balance of the ideal buck converter](buck-stored-energy-sub-eq-integral-suppl.md)
- [Zero net energy change of the buck converter over a returning horizon](buck-stored-energy-periodic-net-change-e.md)

## State-space model and scaling

- [State matrix of the ideal buck converter](buck-matrix.md)
- [Input vector of the ideal buck converter](buck-input.md)
- [The buck state equations in matrix form](buck-matrix-mul-vec-add-smul-buck-input.md)
- [Scaling matrix of the buck state](state-scaling.md)
- [Dimensionless buck state](scaled-state.md)
- [Scaled state matrix of the ideal buck converter](scaled-buck-matrix.md)
- [Scaled input vector of the ideal buck converter](scaled-buck-input.md)
- [The scaled buck matrix is conjugate to the state matrix](state-scaling-mul-scaled-buck-matrix.md)
- [Scaling back the scaled input gives the buck input](state-scaling-mul-vec-scaled-buck-input.md)
- [Scaled buck state matrix as a bounded operator](scaled-buck-operator.md)
- [The scaled buck operator acts by matrix multiplication](scaled-buck-operator-apply.md)
- [The buck state equations in scaled coordinates](scaled-buck-operator-scaled-state-add.md)

## Norms and the averaging error bound

- [Growth-rate bound of the scaled buck dynamics](scaled-buck-growth-rate.md)
- [The scaled buck operator norm is at most the growth-rate bound](norm-scaled-buck-operator-le.md)
- [Maximum norm of the scaled buck input](norm-scaled-buck-input.md)
- [Maximum norm of a difference of scaled states](norm-scaled-state-sub.md)
- [Dimensionless error bound of buck averaging](scaled-buck-error-bound.md)
- [Integral equation of the scaled buck state](scaled-state-integral-eq.md)
- [Error bound between switched and averaged scaled buck states](scaled-state-switched-averaged-error-le.md)
- [Error bound between switched and averaged buck trajectories](buck-switched-averaged-error-le.md)
- [Error bound of buck averaging with a constant duty](buck-switched-averaged-error-le-of-const.md)
