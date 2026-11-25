# Balanced three-phase fault current

A balanced fault through an impedance $Z_f$ at a point whose Thévenin equivalent is a source voltage
$E$ behind an impedance $Z_{\mathrm{th}}$, for one phase of a balanced positive-sequence system with
complex phasors and impedances. For a nonzero total impedance $Z_{\mathrm{th}} + Z_f$ the fault
current is $I_f = E / (Z_{\mathrm{th}} + Z_f)$ and the fault voltage is $V_f = Z_f\, I_f$; the three
phase currents form the balanced positive-sequence set of $I_f$; and for positive phase voltage and
current bases the same formulas hold in per-unit values. The definitions use the convention
$x / 0 = 0$, so $I_f = V_f = 0$ when $Z_{\mathrm{th}} + Z_f = 0$.

- [Thévenin source and balanced fault laws for one phase](is-thevenin-fault.md)
- [Fault current: source voltage over total impedance](fault-current.md)
- [Fault voltage: fault impedance times fault current](fault-voltage.md)
- [Fault phase currents: the balanced set of the fault current](fault-phase-currents.md)

## Solving the fault

- [With nonzero total impedance, the fault laws have exactly one solution](is-thevenin-fault-iff.md)
- [For nonzero total impedance, fault current and voltage solve the laws](is-thevenin-fault-fault-current.md)
- [For nonzero total impedance, fault voltage is E minus Thévenin drop](fault-voltage-eq-sub.md)

## Balanced phase reconstruction

- [A one-phase solution of the fault laws gives a solution in every phase](is-thevenin-fault-balanced-phases.md)
- [For nonzero total impedance, every phase of the fault solves the laws](is-thevenin-fault-fault-phase-currents.md)
- [The fault phase currents are purely positive sequence](sequence-fault-phase-currents.md)

## Physical and per-unit values

- [For positive bases, the fault current formula holds per unit](fault-current-per-unit.md)
- [For positive bases, the fault voltage formula holds per unit](fault-voltage-per-unit.md)
- [For positive bases, the fault laws hold iff they hold per unit](is-thevenin-fault-per-unit-iff.md)
- [For positive bases, the fault phase current formula holds per unit](fault-phase-currents-per-unit.md)

## Bolted faults and degenerate cases

- [A bolted fault has zero fault voltage](fault-voltage-bolted.md)
- [Bolted fault current behind a nonzero pure reactance](fault-current-bolted-reactive.md)
- [Zero total impedance, nonzero source: the fault laws have no solution](not-is-thevenin-fault-of-total-eq-zero.md)
- [Zero total impedance, zero source: every current solves the fault laws](is-thevenin-fault-of-total-eq-zero.md)
- [The phase set I, 0, 0 has all three sequence components equal to I/3](sequence-single-phase.md)
- [A nonzero single-phase set is not a balanced positive-sequence set](single-phase-ne-balanced-phases.md)

## Combined statement

- [With nonzero total impedance: fault solution, sequences, per-unit form](fault-correct.md)
