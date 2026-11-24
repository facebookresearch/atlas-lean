# The closed-form expected number of ones is $NK$ model entry probabilities

For $\alpha > 0$, $N \in \mathbb{N}$ and $K \ge 1$, the [closed-form expected number of ones](expected-ones.md) of the finite feature model equals $NK \cdot \mathbb{P}(z_{ik} = 1)$, where $\mathbb{P}(z_{ik} = 1)$ is the [entry probability](entry-prob.md) computed from the beta–Bernoulli model. Griffiths and Ghahramani obtain the expected number of ones as $K$ times Equation 11, itself the sum of $N$ equal entry probabilities, by linearity of expectation, so this identifies each summand of the closed form with a model probability.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 4.1, Equation 11 and the sentence after it.
