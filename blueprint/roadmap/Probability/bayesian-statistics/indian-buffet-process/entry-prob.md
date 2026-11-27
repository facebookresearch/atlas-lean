# Entry probability of the finite feature model

For $\alpha > 0$ and $K \ge 1$ features, an entry $z_{ik}$ of the finite feature model, with $\pi_k \sim \mathrm{Beta}(\alpha/K, 1)$ and $z_{ik} \mid \pi_k \sim \mathrm{Bernoulli}(\pi_k)$, equals $1$ with probability

$$\frac{\alpha/K}{\alpha/K + 1}.$$

The probability is computed from the model: the Bernoulli likelihood (a single $\mathrm{Bin}(1, \pi_k)$ trial) is integrated against the $\mathrm{Beta}(\alpha/K, 1)$ prior. It is the mean of $\mathrm{Beta}(\alpha/K, 1)$ used in Griffiths and Ghahramani (2011, Section 4.1, Equation 11).

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 4.1, Equation 11.
