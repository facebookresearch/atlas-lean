# Independent Poisson history counts give $\mathrm{Poisson}(\alpha H_N)$ features

Let $\alpha \ge 0$, $N \ge 1$, let $(\Omega, \mathbb{P})$ be a measure space, and let $(K'_h)_{h \in \{0,1\}^N}$ be mutually independent measurable random counts with $K'_h \sim \mathrm{Poisson}(\lambda_h)$ for every non-zero history $h$, where $\lambda_h = \alpha\,(m_h - 1)!\,(N - m_h)!/N!$ is the [history rate](history-rate.md) (the construction of Griffiths and Ghahramani 2011, Section 4.5). Then the total $K_+ = \sum_{h \ne 0} K'_h$ is Poisson with rate $\sum_{h \ne 0} \lambda_h$, which [equals $\alpha H_N$](coe-sum-history-rate.md). Through the Poisson representation, this is the source's statement that the effective dimension of the Indian buffet process is $\mathrm{Poisson}(\alpha H_N)$, which grows like $\alpha \log N$.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Sections 4.5–4.6.
