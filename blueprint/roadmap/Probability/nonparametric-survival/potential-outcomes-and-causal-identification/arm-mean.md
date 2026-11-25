# Mean of a variable within an instrument arm

In a [potential-outcomes model](potential-outcomes.md) with a measure $\mu$, the mean of a real function $f$ in the arm $Z = z$ is

$$\mathbb{E}[f \mid Z = z] = \int f \, d\mu(\cdot \mid Z = z), \qquad \mu(A \mid Z = z) = \frac{\mu(A \cap \{Z = z\})}{\mu(\{Z = z\})},$$

with the conventions that $\mu(\cdot \mid Z = z)$ is the zero measure when $\mu(\{Z = z\})$ is $0$ or infinite, and that the integral of a non-integrable function is $0$.
