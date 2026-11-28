# Equilibrium propagation

Equilibrium propagation trains energy-based recurrent networks with symmetric connections (for example continuous Hopfield networks of leaky-integrator units) using only two relaxations to equilibrium: a free phase and a phase in which the outputs are weakly nudged toward a target. The difference of the local energy gradients between the two equilibria, divided by the nudging strength, converges to the exact gradient of the prediction cost, so a single kind of local computation replaces a separate backpropagation circuit.

- [Equilibrium propagation gradient formula](equilibrium-propagation-gradient-formula.md)
- [Weak clamping decreases the cost at the nudged equilibrium](weak-clamping-decreases-the-cost.md)
