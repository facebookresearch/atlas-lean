# Interval prediction of epidemic trajectories

When the parameters of an epidemic model drift over time (contact rates under changing restrictions, mortality under hospital load), a single fitted trajectory is a poor forecast. Interval predictors instead propagate lower and upper bounds that are guaranteed to enclose every trajectory compatible with parameter, input and initial-condition intervals. For positive discrete-time compartmental models they are built from elementwise monotonicity bounds and certified by induction and linear Lyapunov functions.

- [Interval predictor for a discrete-time SEIR model with time-varying parameters](interval-predictor-for-a-discrete-time-seir-model-with-time-varying-parameters.md)
