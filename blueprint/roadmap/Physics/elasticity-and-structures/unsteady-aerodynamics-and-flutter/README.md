# Unsteady aerodynamics and flutter

- [Theodorsen's unsteady lift on an oscillating airfoil](theodorsen-s-unsteady-lift-on-an-oscillating-airfoil.md)

## Divergence of a typical section

### Quasi-steady moment model

- [Aerodynamic moment on a typical section](aero-moment.md)
- [Net restoring moment on a typical section](restoring-moment.md)
- [Effective torsional stiffness of a typical section](effective-stiffness.md)
- [Divergence dynamic pressure of a typical section](divergence-pressure.md)

### Effective stiffness

- [The restoring moment is affine in the twist](restoring-moment-eq.md)
- [The effective stiffness is the derivative of the restoring moment](has-deriv-at-restoring-moment.md)

### Divergence pressure

- [For a positive aerodynamic factor the divergence pressure is positive](divergence-pressure-pos.md)
- [Positive aerodynamic factor: zero stiffness exactly at divergence](effective-stiffness-eq-zero-iff.md)
- [Positive aerodynamic factor: stiffness is positive below divergence](effective-stiffness-pos-iff.md)
- [Below the divergence pressure only zero twist is in equilibrium](eq-zero-of-restoring-moment-eq-zero.md)
- [For S e C_Lα ≠ 0, every twist balances at the divergence pressure](restoring-moment-divergence-pressure.md)
- [For K, S e C_Lα > 0, a nonzero twist balances at divergence pressure](exists-neutral-displacement.md)

### Nonpositive and zero aerodynamic factor

- [With a nonpositive aerodynamic factor there is no divergence](coupling-nonpos.md)
- [With a zero aerodynamic factor the stiffness never vanishes](coupling-zero.md)

## Flutter of a circulatory two-mode model

### The model and its energy balance

- [Circulatory load operator](circulatory-j.md)
- [Circulatory generalised force](circulatory-force.md)
- [Residual of the circulatory two-mode model](circulatory-residual.md)
- [The circulatory model as a force balance of two unit modes](circulatory-residual-eq-ports.md)
- [Energy balance of the circulatory model](has-deriv-at-energy.md)

### The nonsymmetric circulatory load

- [The circulatory load operator is skew-symmetric](circulatory-j-transpose.md)
- [The circulatory load does no work along the displacement](circulatory-j-mul-vec-dot-product-self.md)
- [The loaded stiffness has the quadratic form of the identity](loaded-stiffness-dot-product-self.md)
- [For nonzero load the loaded stiffness is not symmetric](loaded-stiffness-not-is-symm.md)
- [The loaded stiffness has trivial kernel for every load](loaded-stiffness-mul-vec-eq-zero-iff.md)

### A neutral solution at load 2

- [Neutral trajectory of the circulatory model](neutral-mode.md)
- [Velocity of the neutral trajectory](has-deriv-at-neutral-mode.md)
- [Acceleration of the neutral trajectory](has-deriv-at-deriv-neutral-mode.md)
- [The neutral trajectory solves the model at load 2](neutral-mode-solves.md)
- [The neutral trajectory has unit norm](neutral-mode-dot-product-self.md)
- [On the neutral trajectory the load power balances the damping](neutral-mode-power-balance.md)

### A growing solution at load 8

- [Growing trajectory of the circulatory model](growing-mode.md)
- [Velocity of the growing trajectory](has-deriv-at-growing-mode.md)
- [Acceleration of the growing trajectory](has-deriv-at-deriv-growing-mode.md)
- [The growing trajectory solves the model at load 8](growing-mode-solves.md)
- [The growing trajectory has Euclidean norm e^t](growing-mode-norm.md)
- [The norm of the growing trajectory increases without bound](growing-mode-norm-growing.md)
- [Net power input on the growing trajectory](growing-mode-net-power.md)

### Decay without load

- [Every solution without load is a damped critical response](unloaded-response-eq.md)
- [Without load every solution decays to zero](unloaded-tendsto-zero.md)

### The three sample loads

- [Stable, neutral and growing solutions of the circulatory model](circulatory-witnesses.md)
