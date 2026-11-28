# Closed-form outbreak extinction probability for an SIV model with free virus

**Model.** A host population (for example farmed salmon) with susceptibles $S$, infected hosts $I$ and free virus particles $V$ follows the SIV system

$$
\begin{aligned}
\dot S &= S(\beta - \mu S) - S(I + V), \\
\dot I &= S(I + V) - \alpha I, \\
\dot V &= -\omega V + \delta I,
\end{aligned}
$$

with susceptible birth rate $\beta$, density-dependent mortality $\mu$, infected-host mortality $\alpha$, viral clearance rate $\omega$ and shedding rate $\delta$, all positive. The disease-free equilibrium is $(\bar S,0,0)$ with $\bar S = \beta/\mu$, and

$$
\mathcal R_0 = \frac{(\delta + \omega)\beta}{\alpha\omega\mu},
$$

which is the deterministic threshold: the disease-free equilibrium is globally asymptotically stable iff $\mathcal R_0\le 1$.

**Branching approximation.** In the corresponding continuous-time Markov chain, freeze $S\equiv\bar S$ and pass to the embedded jump chain. Then $(I,V)$ becomes a two-type Galton–Watson process. An infected host dies, sheds a virion or infects a susceptible with probabilities proportional to $\alpha,\delta,\bar S$. A virion is cleared or infects with probabilities proportional to $\omega,\bar S$. The offspring generating function is

$$
\mathbf F(u_1,u_2) = \left(\frac{\alpha + \delta u_1 u_2 + \bar S u_1^2}{\alpha + \delta + \bar S},\ \frac{\omega + \bar S u_1 u_2}{\omega + \bar S}\right),
$$

and its mean matrix is positive, hence primitive.

**Proposition.** Let $q_1,q_2$ be the extinction probabilities of the process started from one infected host or one virion. If $\mathcal R_0\le 1$ then $q_1 = q_2 = 1$. If $\mathcal R_0>1$ then

$$
q_1 = \frac{\alpha + \delta + \omega + \bar S - \sqrt{\bigl(\alpha - (\omega + \bar S)\bigr)^2 + \delta\bigl(\delta + 2(\alpha + \omega + \bar S)\bigr)}}{2\bar S}, \qquad
q_2 = \frac{\omega}{\omega + \bar S(1 - q_1)},
$$

and the probability that the virus dies out from $I(0) = j_1$ infected hosts and $V(0) = j_2$ virions is $\mathbb P_0 = q_1^{j_1}q_2^{j_2}$.

## Expansion

The threshold part is the multitype branching dichotomy. If $\mathbf F(\mathbf 0)>\mathbf 0$, the Jacobian $D\mathbf F$ is monotone on $[0,1]^k$ and $D\mathbf F(\mathbf 1)$ is primitive, then the extinction vector is $\mathbf 1$ when the process is not supercritical. Otherwise it is the unique fixed point of $\mathbf F$ in $[\mathbf 0,\mathbf 1)$. The paper uses $\mathcal R_0$ as the criticality index here; the spectral radius of the mean matrix exceeds $1$ iff $\mathcal R_0>1$. Solving the second fixed-point equation for $q_2$ and substituting into the first gives a cubic with root $q_1 = 1$. Dividing it out leaves a quadratic whose smaller root is the expression above, and that root lies in $(0,1)$ exactly in the supercritical regime. The approximation is accurate only when $\bar S$ is large. For small disease-free populations the frozen-susceptible assumption fails, and the Markov chain's extinction probability must be estimated by simulation.

## Sources

- Evan Milliken, "The Probability of Extinction of Infectious Salmon Anemia Virus in One and Two Patches", Bulletin of Mathematical Biology 79 (2017), 2887–2904, <https://doi.org/10.1007/s11538-017-0355-5>. Published version of arXiv:1611.04406, cited next; locators there refer to the arXiv version.
- Evan Milliken, "The probability of extinction of ISAv in one and two patches", arXiv 2016: Theorem 2.1 (multitype branching extinction criterion), Section 3 (one-patch model: deterministic SIV model, and the stochastic SIV model with its generating function and closed-form extinction probabilities). <https://doi.org/10.48550/arXiv.1611.04406>
