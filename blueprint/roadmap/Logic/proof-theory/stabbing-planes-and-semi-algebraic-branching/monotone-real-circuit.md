# Monotone real circuits

A **monotone real circuit** on Boolean inputs $x_1, \dots, x_N$ is a circuit whose gates compute arbitrary non-decreasing functions $\varphi : \mathbb{R}^2 \to \mathbb{R}$ of their two inputs, with the output interpreted as $1$ if it is at least a threshold. It computes a monotone Boolean function. Monotone real circuits generalize monotone Boolean circuits (gates $\wedge$, $\vee$) and are exactly the model that arises when interpolating cutting planes proofs, where gates add and round down integer linear forms.

## Sources

- P. Pudlák, "Lower bounds for resolution and cutting plane proofs and monotone computations", Journal of Symbolic Logic 62 (1997) 981-998.
- A. Haken, S. A. Cook, "An exponential lower bound for the size of monotone real circuits", Journal of Computer and System Sciences 58 (1999) 326-335.
