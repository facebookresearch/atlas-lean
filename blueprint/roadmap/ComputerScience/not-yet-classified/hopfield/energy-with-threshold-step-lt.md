# Energy descent with thresholds

Let `T` be a symmetric weight matrix (`Matrix.IsSymm T`) and
`U` any thresholds. Then for every neuron `i` and state `v`, if the update of neuron `i` changes the
state (`step T U i v ≠ v`), it strictly decreases the threshold energy:
`energyWithThreshold T U (step T U i v) < energyWithThreshold T U v`.
