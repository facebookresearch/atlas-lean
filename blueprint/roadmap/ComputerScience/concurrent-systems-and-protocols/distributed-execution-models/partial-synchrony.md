# Partial synchrony

In Dwork, Lynch and Stockmeyer's partially synchronous models, there are bounds $\Delta$ on message delivery time and $\Phi$ on relative processor speeds such that either the bounds exist but are not known to the processes, or they are known but hold only after an unknown global stabilization time (GST); in a variant, messages sent before GST may be lost. A protocol is correct for a model if it is correct for every choice of the unknown quantities.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Timed message-passing execution model (processes, steps, message buffer, delivery times, relative speeds).

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988
