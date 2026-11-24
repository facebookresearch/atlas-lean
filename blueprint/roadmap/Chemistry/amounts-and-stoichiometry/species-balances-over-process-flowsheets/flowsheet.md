# Flowsheet

A finite process flowsheet over process units and species. For each
species, every unit obeys a holdup balance whose internal transfer from
unit `i` to unit `j` appears once as an outflow of `i` and once as an
inflow of `j`; external inflow, external outflow, and generation are
supplied separately. This is the single graph type reused by later network
models; dynamics existence is not claimed, since the unit balances are
hypotheses.
