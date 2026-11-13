# Data Law

Law of the whole cell-level data vector. It is defined only for a probability measure `μ` and
a noise process that is a.e.-measurable as a vector-valued map `Ω → (δ × κ → ℝ)`; then the
observation map is a.e.-measurable (`aemeasurable_obs`) and the push-forward is a probability
measure (`isProbabilityMeasure_dataLaw`), not the zero fallback of `Measure.map`.
