# Basis-tracking dynamic flux balance analysis

Dynamic flux balance analysis couples microbial growth and nutrient depletion to a linear program solved at every time step. Because the optimal basis of that linear program typically stays optimal over intervals of time, the fluxes can be followed as a linear function of the time-varying bounds and the program re-solved only when the tracked basic solution would become infeasible.

- [Re-using an optimal basis in community dynamic FBA](re-using-an-optimal-basis-in-community-dynamic-fba.md)
