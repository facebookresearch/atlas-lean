# Steady-state constrained parameter estimation

Perturbation experiments start biochemical systems from an unperturbed steady state, so fitting an ODE model to such data is an optimization over parameters and initial states constrained to the steady-state manifold. The implicit function theorem gives the tangent of that manifold through steady-state sensitivities, which allows moving along it, computing reduced gradients, and turning the constrained problem into an ODE whose stable equilibria are the optima.

- [Steady-state sensitivities and retraction to the steady-state manifold](steady-state-sensitivities-and-retraction-to-the-steady-state-manifold.md)
