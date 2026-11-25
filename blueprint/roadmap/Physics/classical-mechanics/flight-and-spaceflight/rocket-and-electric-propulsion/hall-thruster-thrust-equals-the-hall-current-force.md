# Hall thruster thrust equals the Hall-current force

Consider the acceleration zone $\Omega$ of a Hall thruster, with a steady electric field $E$ and a steady magnetic field $B$ that is transverse to the thrust axis. Assume:
- the plasma is quasi-neutral, $q n_i = e n_e$, where $n_i$ and $n_e$ are the ion and electron densities and $q$ is the ion charge;
- the ions are unmagnetized, so the only force on them is the electric force;
- the electrons have no net axial momentum change in $\Omega$, so the axial electric force on them is balanced by the magnetic force.

Write $J_{\mathrm{Hall}} = -e n_e v_e$ for the current density of the electrons, which drift azimuthally with velocity $v_e = E \times B/|B|^2$.

**Theorem.** Under these assumptions, the axial force on the ions in $\Omega$ equals the Lorentz force on the Hall current,

$$
F_i = \int_\Omega q n_i E\,dV = \int_\Omega J_{\mathrm{Hall}} \times B\,dV,
$$

in the axial component. The reaction to this force acts on the thruster's magnetic circuit, so the force transmitted to the thruster body is $-F_i = -\int_\Omega J_{\mathrm{Hall}} \times B\,dV$, directed against the ion acceleration, and the thrust is its magnitude $T = |F_i|$.

**Proof.** The electrons experience the force density $-e n_e E - e n_e v_e \times B$, and its axial component vanishes by assumption. Quasi-neutrality turns $-e n_e E$ into $-q n_i E$, and the definition of the Hall current turns $-e n_e v_e \times B$ into $J_{\mathrm{Hall}} \times B$. So, axially, $q n_i E = J_{\mathrm{Hall}} \times B$ pointwise. Integrate over $\Omega$. By Newton's third law, the magnetic force of the Hall current on the field sources is equal and opposite to the force of the field on the Hall current.

This force-transfer identity does not determine $J_{\mathrm{Hall}}$, the discharge current or the efficiency. Those require a plasma transport model with anomalous electron mobility, and an electrical port model.

## Background

- [Thrust of an ion beam with divergence factor γ](ion-thrust.md)
- [Thrust efficiency](thrust-efficiency.md)

## Sources

- D. M. Goebel and I. Katz, *Fundamentals of Electric Propulsion: Ion and Hall Thrusters*, JPL Space Science and Technology Series, 2008, <https://descanso.jpl.nasa.gov/SciTechBook/series1/Goebel__cmprsd_opt.pdf>, Section 2.2:
    - the force on unmagnetized ions $F_{\mathrm{ion}} = \int q n_i E$ (2.2-10) and the $E \times B$ electron drift (2.2-11);
    - the axial force balance on the electrons (2.2-12), with quasi-neutrality and $J_{\mathrm{Hall}} = -e n_e v_e$ (2.2-13);
    - $F_i = J_{\mathrm{Hall}} \times B$ (2.2-14), and the thrust on the magnets, equal in magnitude to $J_{\mathrm{Hall}} \times B = F_i$ (2.2-15).
