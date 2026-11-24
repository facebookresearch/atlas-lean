# Is Pipe Flow Equations

Pipe-flow equations on a fixed finite arc topology.
Arc IDs are retained, including parallel pipes. The first
equation says `B *ᵥ q = d`, where `d` is net inflow at nodes.
The second says the head drop from tail to head on each arc is
the quadratic passive law `r e * q e * |q e|`, written in
incidence form as `-Bᵀ *ᵥ h`. No existence, pump, valve,
cavitation, or positive-flow admission claim is included. Resistance
coefficients are unconstrained in this equation relation, so a
negative resistance (an active element) can satisfy it; passivity
is the refinement `IsPassivePipeFlow` below.
