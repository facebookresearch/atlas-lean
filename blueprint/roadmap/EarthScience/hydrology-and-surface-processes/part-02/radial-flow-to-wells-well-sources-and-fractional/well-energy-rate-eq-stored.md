# Production enthalpy from the stored cell state

If every cell `i` stores the fluid mass `m i = φ i * ρc i` per unit volume (porosity `φ i > 0`,
fluid density `ρc i > 0`) and the fluid energy `E i = m i * ec i` (specific internal energy
`ec i`; no rock energy is stored), the produced specific enthalpy `ec i + pc i / ρc i` is
`(E i + φ i * pc i) / m i`, and the [well energy rate](well-energy-rate.md) of cell `i` is
`qI i * hI i - qP i * ((E i + φ i * pc i) / m i)` for all injection rates `qI`, injected
enthalpies `hI` and production rates `qP`: the production withdrawal is fixed by the stored mass
and energy, the porosity and the cell pressure `pc i`.
