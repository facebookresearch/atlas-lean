# The threshold energy is an exact potential

Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`) and `U` any thresholds. Then `energyWithThreshold T U` is an exact potential for
the neuron costs `cost T U`: every unilateral deviation changes the deviating neuron's cost and the
energy by the same amount.
