# Stiffness method for beams and frames

## Beam element stiffness matrix

- [Stiffness matrix of an Euler–Bernoulli beam element](beam-stiffness.md)
- [The beam element stiffness matrix is symmetric](beam-stiffness-transpose.md)
- [A rigid translation produces no beam end forces](beam-stiffness-mul-vec-translation.md)
- [A rigid rotation produces no beam end forces](beam-stiffness-mul-vec-rotation.md)
- [Quadratic form of the beam element stiffness matrix](beam-stiffness-quad-form-factor.md)
- [The beam element stiffness matrix is positive semidefinite](beam-stiffness-pos-semidef.md)
- [The kernel of the beam stiffness matrix is the rigid motions](beam-stiffness-mul-vec-eq-zero-iff.md)

## Local frame element

- [Stiffness matrix of a two-node axial element](axial-stiffness.md)
- [Local stiffness matrix of a planar frame element](frame-stiffness.md)
- [The frame stiffness quadratic form as a sum of squares](frame-stiffness-quad-form-factor.md)
- [Axial and bending energies of a frame element add](frame-stiffness-energy-add.md)
- [The frame element stiffness matrix is symmetric](frame-stiffness-transpose.md)
- [The frame element stiffness matrix is positive semidefinite](frame-stiffness-pos-semidef.md)
- [The kernel of the frame stiffness matrix is the planar rigid motions](frame-stiffness-mul-vec-eq-zero-iff.md)

## Uniform load and end forces

- [Consistent load vector of a uniform load on a beam element](uniform-load-vector.md)
- [Consistent loads of a uniform load from Hermite shape functions](hermite-consistent-loads.md)
- [End deflections and slopes of a beam element](beam-end-data.md)
- [End forces of a beam deflection field](beam-end-forces.md)
- [End forces of a uniformly loaded quartic from the stiffness matrix](quartic-end-force-identity.md)

## Two-span continuous beam

- [Gather matrix of the first span of a two-span beam](span-one-gather.md)
- [Gather matrix of the second span of a two-span beam](span-two-gather.md)
- [Assembled stiffness matrix of a two-span continuous beam](continuous-beam-stiffness.md)
- [Support injection of a beam simply supported at three nodes](support-injection.md)
- [Supported stiffness matrix of a two-span continuous beam](supported-stiffness.md)
- [The first-span gather picks the first four coordinates](span-one-gather-mul-vec.md)
- [The second-span gather picks the last four coordinates](span-two-gather-mul-vec.md)
- [The support injection places the rotations with zero deflections](support-injection-mul-vec.md)
- [The two-span beam energy splits over the spans](continuous-beam-stiffness-quad-form-spli.md)
- [A positive definite supported stiffness gives a unique response](supported-stiffness-exists-unique.md)
- [Supported quadratic form of the two-span beam as sums of squares](supported-stiffness-quad-form-factor.md)
- [The supported two-span beam stiffness is positive definite](supported-stiffness-pos-def.md)
- [A rigid translation is in the kernel of the two-span beam stiffness](continuous-beam-stiffness-mul-vec-transl.md)
- [A rigid rotation about the left end is in the two-span beam kernel](continuous-beam-stiffness-mul-vec-rotati.md)

## Two-span nodal exactness

- [Nodal data of a two-span beam from its span deflections](continuous-beam-nodal-data.md)
- [Assembled consistent load vector of a two-span beam](continuous-beam-load-vector.md)
- [Rotation components of scattered element end forces](support-injection-transpose-scatter.md)
- [Gathered nodal data are the span end data under continuity](gather-continuous-beam-nodal-data.md)
- [The exact nodal slopes solve the supported two-span beam system](supported-stiffness-mul-vec-nodal-slopes.md)
- [Supported finite-element solutions have the exact span end data](continuous-beam-nodal-exact.md)

## Global frame element

- [Global-to-local transformation of a planar frame element](frame-rotation.md)
- [Global stiffness matrix of a planar frame element](frame-stiffness-global.md)
- [The frame transformation is orthogonal: transpose times matrix](frame-rotation-transpose-mul.md)
- [The frame transformation is orthogonal: matrix times transpose](frame-rotation-mul-transpose.md)
- [Round trips through the frame transformation](frame-rotation-mul-vec-round-trip.md)
- [The global frame energy equals the local energy](frame-stiffness-global-quad-form.md)
- [A global translation maps to local translation modes](frame-rotation-mul-vec-global-translatio.md)
- [A global rigid rotation maps to the local rotation mode](frame-rotation-mul-vec-global-rotation.md)
- [The global frame stiffness matrix is symmetric](frame-stiffness-global-transpose.md)
- [The global frame stiffness matrix is positive semidefinite](frame-stiffness-global-pos-semidef.md)
- [Kernel of the global frame stiffness matrix](frame-stiffness-global-mul-vec-eq-zero-i.md)
