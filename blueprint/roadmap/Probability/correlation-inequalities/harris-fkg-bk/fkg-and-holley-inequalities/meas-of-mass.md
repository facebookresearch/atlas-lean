# Finite measure with prescribed point masses

Let $E$ be a finite set and $\mu : \{0,1\}^E \to \mathbb{R}$. The associated measure on $\{0,1\}^E$ is the finite measure

$$m_\mu = \sum_{\omega \in \{0,1\}^E} \max(\mu(\omega), 0)\, \delta_\omega,$$

with point mass $\mu(\omega)$ at each configuration where $\mu(\omega) \ge 0$; negative masses are replaced by $0$. When $\mu \ge 0$ and $\sum_\omega \mu(\omega) = 1$ it is the probability measure with probability mass function $\mu$ ([normalised point masses](meas-of-mass-eq-to-measure.md)).
