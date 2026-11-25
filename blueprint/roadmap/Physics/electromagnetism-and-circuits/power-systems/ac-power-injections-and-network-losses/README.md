# AC power injections and network losses

A finite AC network with node-voltage phasors, branch and shunt admittances and a real node–branch
matrix: branch drops, injected currents and the complex power each node supplies, the balance of the
total supplied power against the branch and shunt terms, the nodal injection equations, and their
per-unit and balanced three-phase forms. The balances hold for all complex data; nonnegativity of
the total real power needs nonnegative conductances.

## Network data and supplied power

- [Branch voltage drop](branch-drop.md)
- [Current injected at a node](node-injection.md)
- [Complex power supplied by a node](node-complex-power.md)
- [Complex power per unit on a direct power base](per-unit-complex-power.md)

## Total power balance

- [Total supplied complex power splits into branch and shunt parts](total-complex-power-eq-branch-add-shunt.md)
- [Total supplied real power equals branch and shunt conductive losses](total-real-power-eq-branch-add-shunt-los.md)
- [Total supplied reactive power is minus the susceptive terms](total-reactive-power-eq-neg-susceptive.md)

## Nodal injection equations

- [Real power at a node: branch injection plus shunt conductance term](node-real-power-eq-branch-add-shunt.md)
- [Reactive power at a node: branch injection minus shunt term](node-reactive-power-eq-branch-sub-shunt.md)

## Sign and per-unit consequences

- [With nonnegative conductances the total real power is nonnegative](total-real-power-nonneg.md)
- [With purely reactive admittances the total real power is zero](total-real-power-eq-zero-of-purely-react.md)
- [For a positive base, per-unit power times the base is the power](per-unit-complex-power-mul-base-eq.md)
- [Direct-base per unit on 3 V_b I_b equals the per-unit power](per-unit-complex-power-three-phase-power.md)
- [3S on the three-phase base and S on V_b I_b give equal per-unit values](per-unit-complex-power-three-mul-three-p.md)

## Balanced three-phase operation

- [A balanced drive makes each node supply three times its phase power](sum-node-complex-power-balanced-phases.md)
- [Balanced three-phase real power is three times the per-phase losses](total-three-phase-real-power-eq-three-mu.md)
