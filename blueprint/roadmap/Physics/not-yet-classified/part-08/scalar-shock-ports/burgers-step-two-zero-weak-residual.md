# Burgers step two zero weak Residual

Fixture: Burgers flux `u ^ 2 / 2` with the nonzero jump from `2` to `0`. At
the Rankine-Hugoniot speed `1` the residual vanishes for every admissible test;
at the incorrect stationary speed `0` it equals `2 * ∫ φ (t, 0) dt`, which is
nonzero exactly when the test has nonzero integral along the front.
