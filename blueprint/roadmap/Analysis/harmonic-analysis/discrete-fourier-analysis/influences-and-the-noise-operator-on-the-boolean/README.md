# Influences and the noise operator on the Boolean cube

## Coordinate flips

- [Coordinate flip on the Boolean cube](flip-coord.md)
- [A coordinate flip negates the flipped coordinate](flip-coord-apply-self.md)
- [A coordinate flip fixes the other coordinates](flip-coord-apply-of-ne.md)
- [Flipping a coordinate twice](flip-coord-flip-coord.md)
- [Flipping a coordinate is an involution](flip-coord-involutive.md)
- [A coordinate flip moves every point](flip-coord-ne-self.md)
- [Sign of a negated Boolean value](cube-val-not.md)
- [Coordinate signs are nonzero](cube-val-ne-zero.md)
- [Coordinate signs have absolute value one](abs-cube-val.md)
- [Flipping a coordinate in a Fourier character](cube-chi-flip-coord.md)
- [Flipping a coordinate preserves sums over the cube](sum-comp-flip-coord.md)
- [Averages are invariant under flipping a coordinate](expect-comp-flip-coord.md)

## Fourier expansion

- [Uniform average over the Boolean cube as a sum](expect-eq-sum-div-two-pow.md)
- [Fourier coefficients as averages](bool-fourier-coeff-eq-expect.md)
- [Fourier coefficients as sums over the cube](bool-fourier-coeff-eq-sum-div-two-pow.md)
- [Average over the Boolean cube as the empty Fourier coefficient](expect-eq-bool-fourier-coeff-empty.md)
- [Orthogonality of the Boolean cube characters](sum-cube-chi-mul-cube-chi-eq-ite.md)
- [Sum of a Boolean cube character](sum-cube-chi-eq-ite.md)
- [Dual orthogonality of the Boolean cube characters](sum-cube-chi-apply-mul-cube-chi-apply-eq.md)
- [Fourier inversion on the Boolean cube](sum-bool-fourier-coeff-mul-cube-chi.md)
- [Plancherel's identity on the Boolean cube](expect-mul-eq-sum-bool-fourier-coeff-mul.md)
- [Parseval's identity on the Boolean cube](expect-sq-eq-sum-bool-fourier-coeff-sq.md)
- [Fourier coefficients determine the function](bool-fourier-coeff-injective.md)
- [Additivity of Fourier coefficients](bool-fourier-coeff-add.md)
- [Fourier coefficients of a difference](bool-fourier-coeff-sub.md)
- [Homogeneity of Fourier coefficients](bool-fourier-coeff-const-mul.md)
- [Fourier coefficients of a constant function](bool-fourier-coeff-const.md)
- [Fourier coefficients of a character](bool-fourier-coeff-cube-chi.md)
- [Uniqueness of the Fourier expansion](bool-fourier-coeff-sum-mul-cube-chi.md)
- [Flipping a coordinate negates the Fourier coefficients of the sets containing it](bool-fourier-coeff-comp-flip-coord.md)

## Influence, total influence and variance

- [Influence of a coordinate](bool-influence.md)
- [Total influence on the Boolean cube](bool-total-influence.md)
- [Variance on the Boolean cube](bool-variance.md)
- [Influences are nonnegative](bool-influence-nonneg.md)
- [Total influence is nonnegative](bool-total-influence-nonneg.md)
- [Variance on the Boolean cube is nonnegative](bool-variance-nonneg.md)
- [Constant functions have zero influence](bool-influence-const.md)
- [Constant functions have zero total influence](bool-total-influence-const.md)
- [Constant functions have zero variance](bool-variance-const.md)
- [Influence of a Boolean function as a flip probability](bool-influence-eq-expect-ite-ne.md)
- [Fourier formula for influence](bool-influence-eq-sum-sq.md)
- [Variance in terms of Fourier coefficients](bool-variance-eq-sum-sq.md)
- [Variance as mean square minus squared mean](bool-variance-eq-expect-sq-sub-sq.md)
- [Total influence in Fourier form](bool-total-influence-eq-sum-card-mul-sq.md)
- [Poincaré inequality on the Boolean cube](bool-variance-le-bool-total-influence.md)

## The noise operator

- [Noise operator on the Boolean cube](bool-noise-op.md)
- [Fourier expansion of the noise operator](bool-noise-op-eq-sum.md)
- [Fourier coefficients of the noise operator](bool-fourier-coeff-bool-noise-op.md)
- [The noise operator $T_1$ is the identity](bool-noise-op-one.md)
- [The noise operator $T_0$ takes the mean](bool-noise-op-zero.md)
- [Semigroup property of the noise operator](bool-noise-op-bool-noise-op.md)
- [The noise operator preserves the mean](expect-bool-noise-op.md)
- [Characters are eigenfunctions of the noise operator](bool-noise-op-cube-chi.md)
- [The noise operator fixes constants](bool-noise-op-const.md)
- [Positivity of the noise operator](bool-noise-op-nonneg.md)
- [Noise stability on the Boolean cube](bool-noise-stab.md)
- [Fourier formula for noise stability](bool-noise-stab-eq-sum.md)
- [Noise stability is at most the second moment](bool-noise-stab-le-expect-sq.md)
- [Noise stability at $\rho = 1$](bool-noise-stab-one.md)
- [Noise stability as a squared norm](bool-noise-stab-sq-eq-expect-sq.md)
- [Noise stability at $\rho = 0$](bool-noise-stab-zero.md)
- [The noise operator is self-adjoint](expect-bool-noise-op-mul-comm.md)
- [Plancherel formula for the noise operator](expect-mul-bool-noise-op-eq-sum.md)
- [Fourier coefficients of the coordinate Laplacian](bool-fourier-coeff-derivative.md)

## Related topics

- [Bonami–Beckner hypercontractivity](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/README.md): norm bounds for the noise operator $T_\rho$, including small-set expansion for noise stability.
- [Kahn–Kalai–Linial inequality](../../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/README.md): a lower bound on the largest influence, from hypercontractivity of $T_\rho$.
- [Structure theorems for Boolean functions](../../../../Combinatorics/boolean-functions/structure-theorems-for-boolean-functions/README.md): FKN, Friedgut's junta theorem and Majority Is Stablest, stated with these influences and noise stability.
- [OSSS inequality for decision trees](../../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/README.md): a variance bound by influences weighted by the query probabilities of a decision tree, refining the Poincaré inequality.
