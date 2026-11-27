# Expectation under independent haplotype sampling

Let $n$ be a natural number, $q \in \mathbb{R}^n$ and $g : \{0, 1\}^n \to \mathbb{R}$. The sampling expectation of $g$ at frequencies $q$ is

$$\mathbb{E}_q[g] = \sum_{x \in \{0, 1\}^n} g(x)\, \pi_q(x),$$

where $\pi_q$ is the [configuration probability](config-prob.md). For $q \in [0, 1]^n$ it is the expectation of $g$ when one haplotype is sampled independently from each population at derived-allele frequencies $q$.
