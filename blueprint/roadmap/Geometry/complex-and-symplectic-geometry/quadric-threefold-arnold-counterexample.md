# A three-fixed-point Hamiltonian counterexample on a projective quadric

Let $Q=\{[z]\in\mathbb CP^4:\sum_{i=0}^4z_i^2=0\}$, with the Fubini–Study form restricted to $Q$. In the unit isotropic cone model, horizontal lifts $v$ satisfy $\sum\overline z_i v_i=\sum z_i v_i=0$, and $\omega(v,w)=2\operatorname{Im}\sum\overline v_iw_i$. There is a Hamiltonian diffeomorphism $\phi$ of $Q$ with exactly three fixed points. The Hamiltonian path is specified by smooth forward and inverse lifts of the isotopy to the unit cone, equivariant under phase, with smooth phase-invariant Hamiltonian and $\iota_{X_t}\omega=dH_t$ on horizontal vectors. It starts at the identity and projects to $\phi$ at time one.

Every smooth real function on $Q$ has at least four critical points, so the infimum of critical-set cardinalities (allowing infinity) is at least $4>3$. Some fixed point of $\phi$ is degenerate: in a local smooth lift fixing a unit representative $z$, some nonzero horizontal $v$ has $DG_zv-v$ in the vertical phase line $\mathbb R iz$. Thus eigenvalue one occurs on the quotient tangent, not just on the unreduced cone. No Morse-only statement is being substituted for the critical-number bound.

## Depends on

- Smooth lifts on the isotropic cone, phase quotient, restricted Fubini–Study form, horizontal differential and extended critical-set cardinality.

## Proof depends on

- Construct the specific Hamiltonian path and exhaust its fixed points, certify horizontal degeneracy, and establish the critical-number lower bound even for degenerate functions.

## Expansion

Prove that local smooth lifts and their derivatives agree on horizontal vectors, then split the fixed-point construction and the critical-number obstruction into separately checkable results.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ArnoldCounterexample.lean#L109-L115) (statement and local definitions).
