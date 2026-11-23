# Observed outcome from potential outcomes

For an event $T$ (treatment) and potential outcomes $Y_0, Y_1 : \Omega \to \mathbb{R}$, the observed outcome is $Y = \mathbf 1_T Y_1 + \mathbf 1_{T^c} Y_0$: it equals $Y_1$ on $T$ and $Y_0$ off it (consistency).

## Background

- [Consistency of counterfactuals](../../../ComputerScience/machine-learning/probabilistic-graphical-models/structural-causal-models-and-counterfactuals/counterfactual-eq-solve.md):
  in a structural causal model, the identity of the observed outcome with the potential outcome
  of the received treatment is a theorem rather than an assumption.
