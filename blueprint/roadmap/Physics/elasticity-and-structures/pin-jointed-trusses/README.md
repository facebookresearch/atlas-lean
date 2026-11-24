# Pin-jointed trusses

Plane trusses of members joined by pins: the compatibility of member extensions with joint
displacements, the equilibrium of member forces with joint loads, and the principle of virtual work
that relates them.

## Compatibility matrices and force collection

- [Joint at an endpoint of a truss member](endpoint-joint.md)
- [Separation-form compatibility matrix of a planar truss](axial-compatibility.md)
- [Unit-direction compatibility matrix of a planar truss](axial-compatibility-unit.md)
- [Row action of the compatibility matrix](axial-compatibility-mul-vec-apply.md)
- [The transposed compatibility matrix collects member end forces](axial-compatibility-transpose-mul-vec-ap.md)
- [The transposed unit compatibility matrix collects axial end forces](axial-compatibility-unit-transpose-mul-v.md)

## Supported stiffness

- [Supported truss stiffness quadratic form as a member sum](supported-quad-form-eq-sum.md)
- [Pairing of supported compatibility and equilibrium](supported-pairing.md)
- [The supported truss stiffness is positive semidefinite](supported-pos-semidef.md)
- [The supported stiffness is the full stiffness restricted by S](supported-stiffness-eq.md)
- [The supported truss stiffness is symmetric](supported-stiffness-is-symm.md)
- [The supported stiffness bilinear form is symmetric](supported-dot-product-mul-vec-comm.md)

## Virtual work

- [The principle of virtual work for a supported plane truss](supported-virtual-work-iff.md)

## Rigidity and unique response

- [Positive definiteness of the supported truss stiffness](supported-pos-def-iff.md)
- [Rigidity of a supported truss with axial weights EA over L cubed](supported-pos-def-iff-of-axial.md)
- [A positive definite supported stiffness gives a unique displacement](supported-exists-unique-of-pos-def.md)
- [Explicit supported displacement by the inverse stiffness](supported-mul-vec-eq-iff-inv-mul-vec.md)
- [Positive weights and no null mode give a unique displacement](supported-exists-unique.md)
- [Unique displacement and residual reaction for a full joint load](supported-residual-exists-unique-of-pos.md)
- [A null mode rules out a unique supported displacement](supported-not-exists-unique-of-kernel.md)
- [Supported truss with axial weights and no null mode: unique response](supported-response-of-axial.md)

## Reciprocal work

- [Reciprocal work for two loads on one supported truss](supported-reciprocal-work.md)

## Load observation and identifiability

- [Load observation matrix of a supported truss](load-observation-matrix.md)
- [Sensor readings are the observation matrix times the load parameters](load-observation-eq-of-supported-eq.md)
- [The inverse-stiffness response solves the system and is observed](load-observation-supported-response.md)
- [With trivial sensor and load kernels, load parameters are identifiable](load-observation-identifiable-on-affine.md)
- [The inverse is not affine on the positive reals](inv-not-affine-on-pos.md)

## Unit-load method

- [Influence vector of a fixed output of a supported truss](influence-vector.md)
- [Unit-load response of a supported truss](unit-load-response.md)
- [The inverse weights recover member length times elongation](supported-inv-diagonal-mul-vec-member-co.md)
- [The influence vector solves the unit-load system](supported-influence-vector-mul-vec.md)
- [Scaling the output scales the influence vector](supported-influence-vector-smul.md)
- [The unit-load response equals the output of the displacement](supported-unit-load-response-eq.md)
- [Unit-load identity in separation form](supported-unit-load-identity-separation.md)
- [Unit-load identity with inverse member weights](supported-unit-load-identity.md)
- [Unit-load identity for positive weights and no null mode](supported-unit-load-identity-of-kernel.md)
- [Unit-load identity in physical axial forces](supported-unit-load-axial-force-identity.md)

## Finite load hull

- [Superposition of unit-load responses over a finite load table](supported-unit-load-response-sum-smul.md)
- [Upper hull bound for the unit-load response](supported-unit-load-response-sum-smul-le.md)
- [Lower hull bound for the unit-load response](supported-inf-le-unit-load-response-sum.md)
- [Hull bounds for the unit-load response of convex load combinations](supported-unit-load-response-convex-comb.md)
- [A convex combination over one load case is that load case](supported-unit-load-response-singleton.md)
- [Absolute hull bound for the unit-load response](supported-abs-unit-load-response-sum-smu.md)
- [Hull bounds for the output of convex load combinations](supported-unit-load-response-convex-comb-2.md)
- [Absolute hull bound for the output of convex load combinations](supported-abs-convex-combination-output.md)

## Determinate trusses

- [Elastic member forces satisfy the reduced equilibrium](reduced-equilibrium-of-elastic.md)
- [Reduced determinate statics with an invertible compatibility matrix](reduced-equilibrium-iff-eq-inv.md)
- [Elastic member forces equal the determinate statics solution](reduced-member-force-eq-inv-mul-vec.md)
- [Determinate member forces do not depend on the axial weights](reduced-member-force-indep-of-diagonal.md)
- [Unique displacement of a determinate system with nonzero weights](reduced-stiffness-exists-unique.md)
- [Unique displacement of a determinate system with positive weights](reduced-stiffness-exists-unique-of-pos.md)
- [Determinate truss member coefficients from statics](truss-reduced-member-coefficient-eq-inv.md)
- [Determinate truss axial forces from statics](truss-reduced-axial-force-eq.md)
